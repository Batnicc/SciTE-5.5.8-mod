// SciTE - Scintilla based Text Editor
/** @file SciTEBase.cxx
 ** Platform independent base class of editor.
 **/
// Copyright 1998-2011 by Neil Hodgson <neilh@scintilla.org>
// The License.txt file describes the conditions under which this software may be distributed.

#include <cstddef>
#include <cstdlib>
#include <cstdint>
#include <cassert>
#include <cstring>
#include <cstdio>
#include <cstdarg>
#include <ctime>
#include <cmath>

#include <system_error>
#include <compare>
#include <tuple>
#include <string>
#include <string_view>
#include <vector>
#include <map>
#include <set>
#include <optional>
#include <algorithm>
#include <memory>
#include <chrono>
#include <atomic>
#include <mutex>
#include <thread>

#include <fcntl.h>
#include <sys/stat.h>

#include "ILoader.h"

#include "ScintillaTypes.h"
#include "ScintillaMessages.h"
#include "ScintillaCall.h"

#include "Scintilla.h"
#include "SciLexer.h"

#include "GUI.h"
#include "ScintillaWindow.h"
#include "StringList.h"
#include "StringHelpers.h"
#include "FilePath.h"
#include "StyleDefinition.h"
#include "PropSetFile.h"
#include "StyleWriter.h"
#include "Extender.h"
#include "SciTE.h"
#include "JobQueue.h"

#include "Cookie.h"
#include "Worker.h"
#include "Utf8_16.h"
#include "FileWorker.h"
#include "MatchMarker.h"
#include "EditorConfig.h"
#include "Searcher.h"
#include "SciTEBase.h"

#include <algorithm>
#include <vector>
#define WIN32_LEAN_AND_MEAN // Исключает редко используемые компоненты (сокеты, GDI и т.д.)
#define NOMINMAX            // Запрещает макросы min и max (они конфликтуют со std::min/max)
#include <windows.h>
#include <array>

Searcher::Searcher() {
	wholeWord = false;
	matchCase = false;
	regExp = false;
	unSlash = false;
	wrapFind = true;
	reverseFind = false;
	filterState = false;
	contextVisible = false;

	searchStartPosition = 0;
	replacing = false;
	havefound = false;
	failedfind = false;
	findInStyle = false;
	findStyle = 0;
	closeFind = CloseFind::closeAlways;

	focusOnReplace = false;
}

void Searcher::InsertFindInMemory() {
	if (!findWhat.empty()) {
		memFinds.InsertDeletePrefix(findWhat);
	}
}

// The find and replace dialogs and strips often manipulate boolean
// flags based on dialog control IDs and menu IDs.
bool &Searcher::FlagFromCmd(int cmd) noexcept {
	static bool notFound = false;
	switch (cmd) {
	case IDWHOLEWORD:
	case IDM_WHOLEWORD:
		return wholeWord;
	case IDMATCHCASE:
	case IDM_MATCHCASE:
		return matchCase;
	case IDREGEXP:
	case IDM_REGEXP:
		return regExp;
	case IDUNSLASH:
	case IDM_UNSLASH:
		return unSlash;
	case IDWRAP:
	case IDM_WRAPAROUND:
		return wrapFind;
	case IDDIRECTIONUP:
	case IDM_DIRECTIONUP:
		return reverseFind;
	case IDFILTERSTATE:
	case IDM_FILTERSTATE:
		return filterState;
	case IDCONTEXTVISIBLE:
	case IDM_CONTEXTVISIBLE:
		return contextVisible;
	}
	return notFound;
}

StyleAndWords::StyleAndWords() {
}

// Set of words separated by spaces. First is style number, rest are symbols.
// <styleNumber> [symbol]*
StyleAndWords::StyleAndWords(const std::string &definition) {
	styleNumber = IntegerFromString(definition, 0);

	std::string_view symbols(definition);

	// Remove initial style number
	const size_t endNumber = symbols.find_first_of(' ');
	if (endNumber == std::string::npos) {
		return;
	}
	symbols.remove_prefix(endNumber + 1);

	words = SetFromString(symbols, ' ');
}

bool StyleAndWords::IsEmpty() const noexcept {
	return words.empty();
}

bool StyleAndWords::IsSingleChar() const noexcept {
	if (words.size() != 1) {
		return false;
	}
	const std::string &first = *words.begin();
	return first.length() == 1;
}

bool StyleAndWords::IsCharacter(char ch) const noexcept {
	if (words.size() != 1) {
		return false;
	}
	const std::string &first = *words.begin();
	return (first.length() == 1) && (ch == first[0]);
}

int StyleAndWords::Style() const noexcept {
	return styleNumber;
}

bool StyleAndWords::Includes(const std::string &value) const {
	if (words.empty()) {
		return false;
	}
	const std::string &first = *words.begin();
	if (first.empty()) {
		return false;
	}
	if (IsAlphabetic(first[0])) {
		return words.count(value) != 0;
	}
	// Set of individual characters. Only one character allowed for now
	const char ch = first[0];
	return value.find(ch) != std::string::npos;
}

UndoBlock::UndoBlock(Scintilla::ScintillaCall &sci_, bool groupNeeded) : sci(sci_) {
	if (groupNeeded) {
		sci.BeginUndoAction();
		// If exception thrown doesn't set began so end is not called
		began = true;
	}
}

UndoBlock::~UndoBlock() noexcept {
	if (began) {
		try {
			sci.EndUndoAction();
		} catch (...) {
			// Must not throw from destructor so ignore exceptions
		}
	}
}

SciTEBase::SciTEBase(Extension *ext) : apis(true), pwFocussed(&wEditor), extender(ext) {
	needIdle = false;
	codePage = 0;
	characterSet = SA::CharacterSet::Ansi;
	language = "java";
	lexLanguage = SCLEX_CPP;
	functionDefinition = "";
	diagnosticStyleStart = 0;
	stripTrailingSpaces = false;
	ensureFinalLineEnd = false;
	ensureConsistentLineEnds = false;
	indentOpening = true;
	indentClosing = true;
	indentMaintain = false;
	statementLookback = 10;
	preprocessorSymbol = '\0';

	tbVisible = false;
	sbVisible = false;
	tabVisible = false;
	tabHideOne = false;
	tabMultiLine = false;
	sbNum = 1;
	visHeightTools = 0;
	visHeightTab = 0;
	visHeightStatus = 0;
	visHeightEditor = 1;
	heightBar = 7;
	dialogsOnScreen = 0;
	topMost = false;
	wrap = false;
	wrapOutput = false;
	wrapStyle = SA::Wrap::Word;
	idleStyling = SA::IdleStyling::None;
	alphaIndicator = static_cast<SA::Alpha>(30);
	underIndicator = false;
	openFilesHere = false;
	fullScreen = false;
	appearance = {};

	heightOutput = heightBar;
	heightEditorSplit = heightBar;
	heightOutputStartDrag = 0;
	previousHeightOutput = 0;
	heightEditorStartDrag = 0;
	previousHeightwEditor2 = 0;

	allowMenuActions = true;
	scrollOutput = 1;
	returnOutputToCommand = true;

	ptStartDrag.x = 0;
	ptStartDrag.y = 0;
	capturedMouse = false;
	firstPropertiesRead = true;
	localiser.read = false;
	splitVertical = false;
	bufferedDraw = true;
	bracesCheck = true;
	bracesSloppy = false;
	bracesStyle = 0;
	braceCount = 0;

	indentationWSVisible = true;
	indentExamine = SA::IndentView::LookBoth;
	autoCompleteIgnoreCase = false;
	imeAutoComplete = false;
	callTipUseEscapes = false;
	callTipIgnoreCase = false;
	autoCCausedByOnlyOne = false;
	autoCompleteVisibleItemCount = 9;
	startCalltipWord = 0;
	currentCallTip = 0;
	maxCallTips = 1;
	currentCallTipWord = "";
	lastPosCallTip = 0;

	margin = false;
	marginWidth = marginWidthDefault;
	foldMargin = true;
	foldMarginWidth = foldMarginWidthDefault;
	lineNumbers = false;
	lineNumbersWidth = lineNumbersWidthDefault;
	lineNumbersExpand = false;

	macrosEnabled = false;
	recording = false;

	propsEmbed.superPS = &propsPlatform;
	propsBase.superPS = &propsEmbed;
	propsUser.superPS = &propsBase;
	propsDirectory.superPS = &propsUser;
	propsLocal.superPS = &propsDirectory;
	propsDiscovered.superPS = &propsLocal;
	props.superPS = &propsDiscovered;

	propsStatus.superPS = &props;

	needReadProperties = false;
	quitting = false;
	canUndo = false;
	canRedo = false;

	timerMask = 0;
	delayBeforeAutoSave = 0;

	editorConfig = IEditorConfig::Create();
}

SciTEBase::~SciTEBase() {
	if (extender)
		extender->Finalise();
	popup.Destroy();
}

void SciTEBase::Finalise() {
	TimerEnd(timerAutoSave);
}

bool SciTEBase::PerformOnNewThread(Worker *pWorker) {
	try {
		std::thread thread([pWorker] {
			pWorker->Execute();
		});
		thread.detach();
		return true;
	} catch (std::system_error &) {
		return false;
	}
}

void SciTEBase::WorkerCommand(int cmd, Worker *pWorker) {
	switch (cmd) {
	case WORK_FILEREAD:
		TextRead(static_cast<FileLoader *>(pWorker));
		UpdateProgress(pWorker);
		break;
	case WORK_FILEWRITTEN:
		TextWritten(static_cast<FileStorer *>(pWorker));
		UpdateProgress(pWorker);
		break;
	case WORK_FILEPROGRESS:
		UpdateProgress(pWorker);
		break;
	}
}

SystemAppearance SciTEBase::CurrentAppearance() const noexcept {
	return {};
}

void SciTEBase::CheckAppearanceChanged() {
	const SystemAppearance currentAppearance = CurrentAppearance();
	if (!(appearance == currentAppearance)) {
		appearance = currentAppearance;
		ReloadProperties();
	}
}

// The system focus may move to other controls including the menu bar
// but we are normally interested in whether the edit or output pane was
// most recently focused and should be used by menu commands.
void SciTEBase::SetPaneFocus(bool editPane) noexcept {
	pwFocussed = editPane ? lEditor : &wOutput;
}

GUI::ScintillaWindow &SciTEBase::PaneFocused() noexcept {
	return wOutput.HasFocus() ? wOutput : wEditor2.HasFocus() ? wEditor2 : wEditor;
}

GUI::ScintillaWindow &SciTEBase::PaneSource(int destination) noexcept {
	if (destination == IDM_SRCWIN)
		return wEditor;
	else if (destination == IDM_SRCWIN2)
		return wEditor2;
	else if (destination == IDM_RUNWIN)
		return wOutput;
	else
		return PaneFocused();
}

intptr_t SciTEBase::CallFocusedElseDefault(int defaultValue, SA::Message msg, uintptr_t wParam, intptr_t lParam) {
	if (wOutput.HasFocus())
		return wOutput.Call(msg, wParam, lParam);
	else if (wEditor.HasFocus())
		return wEditor.Call(msg, wParam, lParam);
	else if (wEditor2.HasFocus())
		return wEditor2.Call(msg, wParam, lParam);
	else
		return defaultValue;
}

void SciTEBase::CallChildren(SA::Message msg, uintptr_t wParam, intptr_t lParam) {
	wEditor.Call(msg, wParam, lParam);
	wEditor2.Call(msg, wParam, lParam);
	wOutput.Call(msg, wParam, lParam);
}

std::string SciTEBase::GetTranslationToAbout(const char *const propname, bool retainIfNotFound) {
#if !defined(GTK)
	return GUI::UTF8FromString(localiser.Text(propname, retainIfNotFound));
#else
	// On GTK, localiser.Text always converts to UTF-8.
	return localiser.Text(propname, retainIfNotFound);
#endif
}

void SciTEBase::ViewWhitespace(bool view) {
	if (view && indentationWSVisible == 2)
	{
		wEditor.SetViewWS(SA::WhiteSpace::VisibleOnlyInIndent);
		wEditor2.SetViewWS(SA::WhiteSpace::VisibleOnlyInIndent);
	}
	else if (view && indentationWSVisible)
	{
		wEditor.SetViewWS(SA::WhiteSpace::VisibleAlways);
		wEditor2.SetViewWS(SA::WhiteSpace::VisibleAlways);
	}
	else if (view)
	{
		wEditor.SetViewWS(SA::WhiteSpace::VisibleAfterIndent);
		wEditor2.SetViewWS(SA::WhiteSpace::VisibleAfterIndent);
	}
	else
	{
		wEditor.SetViewWS(SA::WhiteSpace::Invisible);
		wEditor2.SetViewWS(SA::WhiteSpace::Invisible);
	}
}

StyleAndWords SciTEBase::GetStyleAndWords(const char *base) {
	const std::string fileNameForExtension = ExtensionFileName();
	const std::string sAndW = props.GetNewExpandString(base, fileNameForExtension);
	return StyleAndWords(sAndW);
}

void SciTEBase::AssignKey(SA::Keys key, SA::KeyMod mods, int cmd) {
	wEditor.AssignCmdKey(
		IntFromTwoShorts(static_cast<short>(key),
				 static_cast<short>(mods)), cmd);
	wEditor2.AssignCmdKey(
		IntFromTwoShorts(static_cast<short>(key),
			static_cast<short>(mods)), cmd);
}

/**
 * Override the language of the current file with the one indicated by @a cmdID.
 * Mostly used to set a language on a file of unknown extension.
 */
void SciTEBase::SetOverrideLanguage(int cmdID) {
	const FilePosition fp = GetFilePosition();
	EnsureRangeVisible(*lEditor, SA::Span(0, lEditor->Length()), false);
	// Zero all the style bytes
	lEditor->ClearDocumentStyle();

	CurrentBuffer()->overrideExtension = "x.";
	CurrentBuffer()->overrideExtension += languageMenu[cmdID].extension;
	ReadProperties();
	SetIndentSettings();
	lEditor->ColouriseAll();
	Redraw();
	DisplayAround(fp);
}

SA::Position SciTEBase::LengthDocument() {
	return wEditor.Length();
}

SA::Position SciTEBase::GetCaretInLine() {
	const SA::Position caret = lEditor->CurrentPos();
	const SA::Line line = lEditor->LineFromPosition(caret);
	const SA::Position lineStart = lEditor->LineStart(line);
	return caret - lineStart;
}

std::string SciTEBase::GetLine(SA::Line line) {
	const SA::Span rangeLine(wEditor.LineStart(line), wEditor.LineEnd(line));
	return wEditor.StringOfRange(rangeLine);
}

std::string SciTEBase::GetCurrentLine() {
	// Get needed buffer size
	const SA::Position len = lEditor->GetCurLine(0, nullptr);
	// Allocate buffer, including space for NUL
	std::string text(len, '\0');
	// And get the line
	lEditor->GetCurLine(len, text.data());
	return text;
}

/**
 * Check if the given line is a preprocessor condition line.
 * @return The kind of preprocessor condition (enum values).
 */
SciTEBase::PreProc SciTEBase::LinePreprocessorCondition(SA::Line line) {
	const std::string text = GetLine(line);

	const char *currChar = text.c_str();

	while (IsASpace(*currChar)) {
		currChar++;
	}
	if (preprocessorSymbol && (*currChar == preprocessorSymbol)) {
		currChar++;
		while (IsASpace(*currChar)) {
			currChar++;
		}
		std::string word;
		while (*currChar && !IsASpace(*currChar)) {
			word.push_back(*currChar++);
		}
		std::map<std::string, PreProc>::const_iterator it = preprocOfString.find(word);
		if (it != preprocOfString.end()) {
			return it->second;
		}
	}
	return PreProc::None;
}

/**
 * Search a matching preprocessor condition line.
 * @return @c true if the end condition are meet.
 * Also set curLine to the line where one of these conditions is mmet.
 */
bool SciTEBase::FindMatchingPreprocessorCondition(
	SA::Line &curLine,   		///< Number of the line where to start the search
	int direction,   		///< Direction of search: 1 = forward, -1 = backward
	PreProc condEnd1,   		///< First status of line for which the search is OK
	PreProc condEnd2) {		///< Second one

	bool isInside = false;
	int level = 0;
	const SA::Line maxLines = lEditor->LineCount() - 1;

	while (curLine < maxLines && curLine > 0 && !isInside) {
		curLine += direction;	// Increment or decrement
		const PreProc status = LinePreprocessorCondition(curLine);

		if ((direction == 1 && status == PreProc::Start) || (direction == -1 && status == PreProc::End)) {
			level++;
		} else if (level > 0 && ((direction == 1 && status == PreProc::End) || (direction == -1 && status == PreProc::Start))) {
			level--;
		} else if (level == 0 && (status == condEnd1 || status == condEnd2)) {
			isInside = true;
		}
	}

	return isInside;
}

/**
 * Find if there is a preprocessor condition after or before the caret position,
 * @return @c true if inside a preprocessor condition.
 */
bool SciTEBase::FindMatchingPreprocCondPosition(
	bool isForward,   		///< @c true if search forward
	SA::Position mppcAtCaret,   	///< Matching preproc. cond.: current position of caret
	SA::Position &mppcMatch) {		///< Matching preproc. cond.: matching position

	bool isInside = false;

	// Get current line
	SA::Line curLine = lEditor->LineFromPosition(mppcAtCaret);
	const PreProc status = LinePreprocessorCondition(curLine);

	switch (status) {
	case PreProc::Start:
		if (isForward) {
			isInside = FindMatchingPreprocessorCondition(curLine, 1,
					PreProc::Middle, PreProc::End);
		} else {
			mppcMatch = mppcAtCaret;
			return true;
		}
		break;
	case PreProc::Middle:
		if (isForward) {
			isInside = FindMatchingPreprocessorCondition(curLine, 1,
					PreProc::Middle, PreProc::End);
		} else {
			isInside = FindMatchingPreprocessorCondition(curLine, -1,
					PreProc::Start, PreProc::Middle);
		}
		break;
	case PreProc::End:
		if (isForward) {
			mppcMatch = mppcAtCaret;
			return true;
		} else {
			isInside = FindMatchingPreprocessorCondition(curLine, -1,
					PreProc::Start, PreProc::Middle);
		}
		break;
	default:   	// Should be noPPC

		if (isForward) {
			isInside = FindMatchingPreprocessorCondition(curLine, 1,
					PreProc::Middle, PreProc::End);
		} else {
			isInside = FindMatchingPreprocessorCondition(curLine, -1,
					PreProc::Start, PreProc::Middle);
		}
		break;
	}

	if (isInside) {
		mppcMatch = lEditor->LineStart(curLine);
	}
	return isInside;
}

namespace {

constexpr bool IsBrace(char ch) noexcept {
	return ch == '[' || ch == ']' || ch == '(' || ch == ')' || ch == '{' || ch == '}';
}

}

/**
 * Find if there is a brace next to the caret, checking before caret first, then
 * after caret. If brace found also find its matching brace.
 * @return @c true if inside a bracket pair.
 */
bool SciTEBase::FindMatchingBracePosition(bool editor, SA::Position &braceAtCaret, SA::Position &braceOpposite, bool sloppy) {
	bool isInside = false;
	GUI::ScintillaWindow &win = editor ? *lEditor : wOutput;

	const int mainSel = win.MainSelection();
	if (win.SelectionNCaretVirtualSpace(mainSel) > 0)
		return false;

	const int bracesStyleCheck = editor ? bracesStyle : 0;
	SA::Position caretPos = win.CurrentPos();
	braceAtCaret = -1;
	braceOpposite = -1;
	char charBefore = '\0';
	int styleBefore = 0;
	const SA::Position lengthDoc = win.Length();
	if ((lengthDoc > 0) && (caretPos > 0)) {
		// Check to ensure not matching brace that is part of a multibyte character
		if (win.PositionBefore(caretPos) == (caretPos - 1)) {
			charBefore = win.CharacterAt(caretPos - 1);
			styleBefore = win.UnsignedStyleAt(caretPos - 1);
		}
	}
	// Priority goes to character before caret
	if (charBefore && IsBrace(charBefore) &&
			((styleBefore == bracesStyleCheck) || (!bracesStyle))) {
		braceAtCaret = caretPos - 1;
	}
	bool colonMode = false;
	if ((lexLanguage == SCLEX_PYTHON) &&
			(':' == charBefore) && (SCE_P_OPERATOR == styleBefore)) {
		braceAtCaret = caretPos - 1;
		colonMode = true;
	}
	bool isAfter = true;
	if (lengthDoc > 0 && sloppy && (braceAtCaret < 0) && (caretPos < lengthDoc)) {
		// No brace found so check other side
		// Check to ensure not matching brace that is part of a multibyte character
		if (win.PositionAfter(caretPos) == (caretPos + 1)) {
			const char charAfter = win.CharacterAt(caretPos);
			const int styleAfter = win.UnsignedStyleAt(caretPos);
			if (charAfter && IsBrace(charAfter) && ((styleAfter == bracesStyleCheck) || (!bracesStyle))) {
				braceAtCaret = caretPos;
				isAfter = false;
			}
			if ((lexLanguage == SCLEX_PYTHON) &&
					(':' == charAfter) && (SCE_P_OPERATOR == styleAfter)) {
				braceAtCaret = caretPos;
				colonMode = true;
			}
		}
	}
	if (braceAtCaret >= 0) {
		if (colonMode) {
			const SA::Line lineStart = win.LineFromPosition(braceAtCaret);
			const SA::Line lineMaxSubord = win.LastChild(lineStart, static_cast<SA::FoldLevel>(-1));
			braceOpposite = win.LineEnd(lineMaxSubord);
		} else {
			braceOpposite = win.BraceMatch(braceAtCaret, 0);
		}
		if (braceOpposite > braceAtCaret) {
			isInside = isAfter;
		} else {
			isInside = !isAfter;
		}
	}
	return isInside;
}

void SciTEBase::BraceMatch(bool editor) {
	if (!bracesCheck)
		return;
	SA::Position braceAtCaret = -1;
	SA::Position braceOpposite = -1;
	FindMatchingBracePosition(editor, braceAtCaret, braceOpposite, bracesSloppy);
	GUI::ScintillaWindow &win = editor ? *lEditor : wOutput;
	if ((braceAtCaret != -1) && (braceOpposite == -1)) {
		win.BraceBadLight(braceAtCaret);
		lEditor->SetHighlightGuide(0);
	} else {
		char chBrace = 0;
		if (braceAtCaret >= 0)
			chBrace = win.CharacterAt(braceAtCaret);
		win.BraceHighlight(braceAtCaret, braceOpposite);
		SA::Position columnAtCaret = win.Column(braceAtCaret);
		SA::Position columnOpposite = win.Column(braceOpposite);
		if (chBrace == ':') {
			const SA::Line lineStart = win.LineFromPosition(braceAtCaret);
			const SA::Position indentPos = win.LineIndentPosition(lineStart);
			const SA::Position indentPosNext = win.LineIndentPosition(lineStart + 1);
			columnAtCaret = win.Column(indentPos);
			const SA::Position columnAtCaretNext = win.Column(indentPosNext);
			const int indentSize = win.Indent();
			if (columnAtCaretNext - indentSize > 1)
				columnAtCaret = columnAtCaretNext - indentSize;
			if (columnOpposite == 0)	// If the final line of the structure is empty
				columnOpposite = columnAtCaret;
		} else {
			if (win.LineFromPosition(braceAtCaret) == win.LineFromPosition(braceOpposite)) {
				// Avoid attempting to draw a highlight guide
				columnAtCaret = 0;
				columnOpposite = 0;
			}
		}

		if (props.GetInt("highlight.indentation.guides"))
			win.SetHighlightGuide(std::min(columnAtCaret, columnOpposite));
	}
}

void SciTEBase::SetWindowName() {
	if (filePath.IsUntitled()) {
		windowName = localiser.Text("Untitled");
		windowName.insert(0, GUI_TEXT("("));
		windowName += GUI_TEXT(")");
	} else if (props.GetInt("title.full.path") == 2) {
		windowName = FileNameExt().AsInternal();
		windowName += GUI_TEXT(" ");
		windowName += localiser.Text("in");
		windowName += GUI_TEXT(" ");
		windowName += filePath.Directory().AsInternal();
	} else if (props.GetInt("title.full.path") == 1) {
		windowName = filePath.AsInternal();
	} else {
		windowName = FileNameExt().AsInternal();
	}
	if (CurrentBufferConst()->isReadOnly)
		windowName += GUI_TEXT(" |");
	if (CurrentBufferConst()->isDirty)
		windowName += GUI_TEXT("*");
	else
		windowName += GUI_TEXT(" - ");
	windowName += appName;

	if (buffers.length > 1 && props.GetInt("title.show.buffers")) {
		windowName += GUI_TEXT(" [");
		windowName += GUI::StringFromInteger(buffers.Current() + 1);
		windowName += GUI_TEXT(" ");
		windowName += localiser.Text("of");
		windowName += GUI_TEXT(" ");
		windowName += GUI::StringFromInteger(buffers.length);
		windowName += GUI_TEXT("]");
	}

	wSciTE.SetTitle(windowName.c_str());
}

SA::Span SciTEBase::GetSelection() {
	return lEditor->SelectionSpan();
}

SelectedRange SciTEBase::GetSelectedRange(GUI::ScintillaWindow &wEditor) {
	return SelectedRange(wEditor.CurrentPos(), wEditor.Anchor());
}

void SciTEBase::SetSelection(SA::Position anchor, SA::Position currentPos, GUI::ScintillaWindow &wEditor) {
	wEditor.SetSel(anchor, currentPos);
}

std::string SciTEBase::GetCTag(GUI::ScintillaWindow *pw) {
	const SA::Position lengthDoc = pw->Length();
	SA::Position selEnd = pw->SelectionEnd();
	SA::Position selStart = selEnd;
	TextReader acc(*pw);
	int mustStop = 0;
	while (!mustStop) {
		if (selStart < lengthDoc - 1) {
			selStart++;
			const char c = acc[selStart];
			if (c == '\r' || c == '\n') {
				mustStop = -1;
			} else if (c == '\t' && ((acc[selStart + 1] == '/' && acc[selStart + 2] == '^') || IsADigit(acc[selStart + 1]))) {
				mustStop = 1;
			}
		} else {
			mustStop = -1;
		}
	}
	if (mustStop == 1 && (acc[selStart + 1] == '/' && acc[selStart + 2] == '^')) {	// Found
		selEnd = selStart += 3;
		mustStop = 0;
		while (!mustStop) {
			if (selEnd < lengthDoc - 1) {
				selEnd++;
				const char c = acc[selEnd];
				if (c == '\r' || c == '\n') {
					mustStop = -1;
				} else if (c == '$' && acc[selEnd + 1] == '/') {
					mustStop = 1;	// Found!
				}

			} else {
				mustStop = -1;
			}
		}
	} else if (mustStop == 1 && IsADigit(acc[selStart + 1])) {
		// a Tag can be referenced by line Number also
		selEnd = selStart += 1;
		while ((selEnd < lengthDoc) && IsADigit(acc[selEnd])) {
			selEnd++;
		}
	}

	if (selStart < selEnd) {
		return pw->StringOfRange(SA::Span(selStart, selEnd));
	} else {
		return std::string();
	}
}

void SciTEBase::DropSelectionAt(GUI::ScintillaWindow &win, int selection) {
	if (win.SelectionMode() != SA::SelectionMode::Stream) {
		return;
	}
	if (selection >= 0) {
		win.DropSelectionN(selection);
	}
}

// Default characters that can appear in a word
bool SciTEBase::iswordcharforsel(char ch) noexcept {
	return !strchr("\t\n\r !\"#$%&'()*+,-./:;<=>?@[\\]^`{|}~", ch);
}

// Accept slightly more characters than for a word
// Doesn't accept all valid characters, as they are rarely used in source filenames...
// Accept path separators '/' and '\', extension separator '.', and ':', MS drive unit
// separator, and also used for separating the line number for grep. Same for '(' and ')' for cl.
// Accept '?' and '%' which are used in URL.
bool SciTEBase::isfilenamecharforsel(char ch) noexcept {
	return !strchr("\t\n\r \"$'*,;<>[]^`{|}", ch);
}

bool SciTEBase::islexerwordcharforsel(char ch) noexcept {
	// If there are no word.characters defined for the current file, fall back on the original function
	if (wordCharacters.length())
		return Contains(wordCharacters, ch);
	else
		return iswordcharforsel(ch);
}

void SciTEBase::HighlightCurrentWord(bool highlight) {
	if (!currentWordHighlight.isEnabled)
		return;
	if (!wEditor.HasFocus() && !wEditor2.HasFocus() && !wOutput.HasFocus() && highlight) {
		// Neither text window has focus, possibly app is inactive so do not highlight
		return;
	}
	GUI::ScintillaWindow &wCurrent = wOutput.HasFocus() ? wOutput : *lEditor;
	// Remove old indicators if any exist.
	wCurrent.SetIndicatorCurrent(indicatorHighlightCurrentWord);
	const SA::Position lenDoc = wCurrent.Length();
	wCurrent.IndicatorClearRange(0, lenDoc);
	if (!highlight)
		return;
	if (FilterShowing()) {
		return;
	}
	// Get start & end selection.
	SA::Span sel = wCurrent.SelectionSpan();
	const bool noUserSelection = sel.start == sel.end;
	std::string sWordToFind = RangeExtendAndGrab(wCurrent, sel,
				  &SciTEBase::islexerwordcharforsel);
	if (sWordToFind.length() == 0 || (sWordToFind.find_first_of("\n\r ") != std::string::npos))
		return; // No highlight when no selection or multi-lines selection.
	if (noUserSelection && currentWordHighlight.statesOfDelay == CurrentWordHighlight::StatesOfDelay::noDelay) {
		// Manage delay before highlight when no user selection but there is word at the caret.
		currentWordHighlight.statesOfDelay = CurrentWordHighlight::StatesOfDelay::delay;
		// Reset timer
		currentWordHighlight.elapsedTimes.Duration(true);
		return;
	}
	// Get style of the current word to highlight only word with same style.
	int selectedStyle = wCurrent.UnsignedStyleAt(sel.start);
	if (!currentWordHighlight.isOnlyWithSameStyle)
		selectedStyle = -1;

	// Manage word with DBCS.
	const std::string wordToFind = EncodeString(sWordToFind);

	const SA::FindOption searchFlags = SA::FindOption::MatchCase | SA::FindOption::WholeWord;
	matchMarker.StartMatch(&wCurrent, wordToFind,
			       searchFlags, selectedStyle,
			       indicatorHighlightCurrentWord, -1);
	SetIdler(true);
}

std::string SciTEBase::GetRangeInUIEncoding(GUI::ScintillaWindow &win, SA::Span span) {
	return win.StringOfRange(span);
}

std::string SciTEBase::GetLine(GUI::ScintillaWindow &win, SA::Line line) {
	const SA::Position lineStart = win.LineStart(line);
	const SA::Position lineEnd = win.LineEnd(line);
	if ((lineStart < 0) || (lineEnd < 0))
		return std::string();
	return win.StringOfRange(SA::Span(lineStart, lineEnd));
}

void SciTEBase::RangeExtend(
	GUI::ScintillaWindow &wCurrent,
	SA::Span &span,
	bool (SciTEBase::*ischarforsel)(char ch)) {	///< Function returning @c true if the given char. is part of the selection.
	if (span.start == span.end) {
		// Empty span and have a function to extend it
		const SA::Position lengthDoc = wCurrent.Length();
		TextReader acc(wCurrent);
		// Try and find a word at the caret
		// On the left...
		while ((span.start > 0) && ((this->*ischarforsel)(acc[span.start - 1]))) {
			span.start--;
		}
		// and on the right
		while ((span.end < lengthDoc) && ((this->*ischarforsel)(acc[span.end]))) {
			span.end++;
		}
	}
}

std::string SciTEBase::RangeExtendAndGrab(
	GUI::ScintillaWindow &wCurrent,
	SA::Span &span,
	bool (SciTEBase::*ischarforsel)(char ch),	///< Function returning @c true if the given char. is part of the selection.
	bool stripEol /*=true*/) {

	RangeExtend(wCurrent, span, ischarforsel);
	std::string selected = GetRangeInUIEncoding(wCurrent, span);
	if (stripEol) {
		// Whole line may be selected but normally end of line characters not wanted.
		StripEOL(selected);
	}

	return selected;
}

/**
 * If there is selected text, either in the editor or the output pane,
 * return the selected text.
 * Otherwise, try and select characters around the caret, as long as they are OK
 * for the @a ischarforsel function.
 * For @a stripEol, remove one trailing line end if present.
 */
std::string SciTEBase::SelectionExtend(
	bool (SciTEBase::*ischarforsel)(char ch),	///< Function returning @c true if the given char. is part of the selection.
	bool stripEol /*=true*/) {

	SA::Span sel = pwFocussed->SelectionSpan();
	return RangeExtendAndGrab(*pwFocussed, sel, ischarforsel, stripEol);
}

std::string SciTEBase::SelectionWord(bool stripEol /*=true*/) {
	return SelectionExtend(&SciTEBase::islexerwordcharforsel, stripEol);
}

std::string SciTEBase::SelectionFilename() {
	return SelectionExtend(&SciTEBase::isfilenamecharforsel);
}

void SciTEBase::SelectionIntoProperties() {
	const SA::Span range = pwFocussed->SelectionSpan();

	const std::string currentSelection = GetRangeInUIEncoding(*pwFocussed, range);
	props.Set("CurrentSelection", currentSelection);

	const std::string word = SelectionWord();
	props.Set("CurrentWord", word);

	props.Set("SelectionStartLine", std::to_string(pwFocussed->LineFromPosition(range.start) + 1));
	props.Set("SelectionStartColumn", std::to_string(pwFocussed->Column(range.start) + 1));
	props.Set("SelectionEndLine", std::to_string(pwFocussed->LineFromPosition(range.end) + 1));
	props.Set("SelectionEndColumn", std::to_string(pwFocussed->Column(range.end) + 1));
}

void SciTEBase::SelectionIntoFind(bool stripEol /*=true*/) {
	const std::string sel = SelectionWord(stripEol);
	if (sel.length()) { // && (sel.find_first_of("\r\n") == std::string::npos)) {
		// The selection does not include a new line, so is likely to be
		// the expression to search...
		findWhat = sel;
		if (unSlash) {
			findWhat = Slash(findWhat, false);
		}
	}
	// else findWhat remains the same as last time.
}

void SciTEBase::SelectionAdd(AddSelection add) {
	SA::FindOption flags = SA::FindOption::None;
	if (!pwFocussed->SelectionEmpty()) {
		// If selection is word then match as word.
		if (pwFocussed->IsRangeWord(pwFocussed->SelectionStart(),
					    pwFocussed->SelectionEnd()))
			flags = SA::FindOption::WholeWord;
	}
	pwFocussed->TargetWholeDocument();
	pwFocussed->SetSearchFlags(flags);
	if (add == AddSelection::next) {
		pwFocussed->MultipleSelectAddNext();
	} else {
		if (pwFocussed->SelectionEmpty()) {
			pwFocussed->MultipleSelectAddNext();
		}
		pwFocussed->MultipleSelectAddEach();
	}
}

std::string SciTEBase::EncodeString(const std::string &s) {
	return s;
}

namespace {

constexpr int minimumSplit = 20;
constexpr int baseSplitHorizontal = 300;
constexpr int baseSplitVertical = 100;

std::string UnSlashAsNeeded(const std::string &s, bool escapes, bool regularExpression) {
	if (escapes) {
		if (regularExpression) {
			// For regular expressions, the only escape sequences allowed start with \0
			// Other sequences, like \t, are handled by the RE engine.
			return UnSlashLowOctalString(s);
		}
		// C style escapes allowed
		return UnSlashString(s);
	}
	return s;
}

}

void SciTEBase::RemoveFindMarks() {
	findMarker.Stop();	// Cancel ongoing background find
	if (CurrentBuffer()->findMarks != Buffer::FindMarks::none) {
		lEditor->SetIndicatorCurrent(indicatorMatch);
		lEditor->IndicatorClearRange(0, LengthDocument());
		CurrentBuffer()->findMarks = Buffer::FindMarks::none;
	}
	lEditor->MarkerDeleteAll(markerFilterMatch);
	lEditor->AnnotationClearAll();
}

SA::FindOption SciTEBase::SearchFlags(bool regularExpressions) const {
	SA::FindOption opt = SA::FindOption::None;
	if (wholeWord)
		opt |= SA::FindOption::WholeWord;
	if (matchCase)
		opt |= SA::FindOption::MatchCase;
	if (regularExpressions)
		opt |= SA::FindOption::RegExp;
	if (props.GetInt("find.replace.regexp.posix"))
		opt |= SA::FindOption::Posix;
	if (props.GetInt("find.replace.regexp.cpp11"))
		opt |= SA::FindOption::Cxx11RegEx;
	return opt;
}

void SciTEBase::MarkAll(MarkPurpose purpose) {
	lEditor->MarkerDeleteAll(markerBookmark);
	RemoveFindMarks();
	lEditor->SetIndicatorCurrent(indicatorMatch);

	int bookMark = -1;
	std::optional<SA::Line> contextLines;

	const SA::IndicatorNumbers indicatorNumMatch = static_cast<SA::IndicatorNumbers>(indicatorMatch);

	if (purpose == MarkPurpose::incremental) {
		CurrentBuffer()->findMarks = Buffer::FindMarks::temporary;
		SetOneIndicator(*lEditor, indicatorNumMatch,
			IndicatorDefinition(props.Get("find.indicator.incremental")));
	} else if (purpose == MarkPurpose::filter) {
		CurrentBuffer()->findMarks = Buffer::FindMarks::temporary;
		SetOneIndicator(*lEditor, indicatorNumMatch,
				IndicatorDefinition(props.Get("filter.match.indicator")));
		bookMark = markerFilterMatch;
		contextLines = contextVisible ? props.GetInt("filter.context", 2) : 0;
	} else {
		CurrentBuffer()->findMarks = Buffer::FindMarks::marked;
		const std::string_view findIndicatorString = props.Get("find.mark.indicator");
		IndicatorDefinition findIndicator(findIndicatorString);
		if (!findIndicatorString.length()) {
			findIndicator.style = SA::IndicatorStyle::RoundBox;
			const std::string_view findMark = props.Get("find.mark");
			if (findMark.length())
				findIndicator.colour = ColourFromString(findMark);
			findIndicator.fillAlpha = alphaIndicator;
			findIndicator.under = underIndicator;
		}
		SetOneIndicator(*lEditor, indicatorNumMatch, findIndicator);
		bookMark = markerBookmark;
	}

	const std::string findTarget = UnSlashAsNeeded(EncodeString(findWhat), unSlash, regExp);
	if (findTarget.length() == 0) {
		return;
	}

	findMarker.StartMatch(lEditor, findTarget,
			      SearchFlags(regExp), -1,
			      indicatorMatch, bookMark, contextLines);
	SetIdler(true);
	SyncMarkersToMap();
}

void SciTEBase::FilterAll(bool showMatches) {

	HighlightCurrentWord(false);
	wEditor.MarkerDeleteAll(markerFilterMatch);

	if (!showMatches || findWhat.empty()) {
		RemoveFindMarks();
		// Show all lines
		wEditor.ShowLines(0, wEditor.LineFromPosition(wEditor.Length()));
		// Restore fold margin
		wEditor.SetMarginWidthN(2, foldMargin ? foldMarginWidth : 0);
		// May have selected something in filter so scroll to it
		wEditor.ScrollCaret();
		RestoreFolds(CurrentBuffer()->foldState);
		return;
	}

	// Hide fold margin as the shapes will overlap hidden lines and not make sense
	wEditor.SetMarginWidthN(2, 0);

	wEditor.SetRedraw(false);
	wEditor.SetSearchFlags(SearchFlags(regExp));

	MarkAll(Searcher::MarkPurpose::filter);
	wEditor.SetRedraw(true);
}

int SciTEBase::IncrementSearchMode() {
	FindIncrement();
	return 0;
}

int SciTEBase::FilterSearch() {
	Filter();
	return 0;
}

void SciTEBase::FailedSaveMessageBox(const FilePath &filePathSaving) {
	const GUI::gui_string msg = LocaliseMessage(
					    "Could not save file \"^0\".", filePathSaving.AsInternal());
	WindowMessageBox(wSciTE, msg);
}

bool SciTEBase::FindReplaceAdvanced() const {
	return props.GetInt("find.replace.advanced");
}

SA::Position SciTEBase::FindInTarget(const std::string &findWhatText, SA::Span range, bool notEmptyAtStartRegEx) {
	lEditor->SetTarget(range);
	SA::Position posFind = lEditor->SearchInTarget(findWhatText);
	if (notEmptyAtStartRegEx) {
		if ((posFind == range.start) && (lEditor->TargetEnd() == posFind)) {
			if (range.start == range.end) {
				return SA::InvalidPosition;
			} else if (range.start < range.end) {
				range.start = lEditor->PositionAfter(range.start);
				if (range.start > range.end) {
					return SA::InvalidPosition;
				}
			} else {
				range.start = lEditor->PositionBefore(range.start);
				if (range.start < range.end) {
					return SA::InvalidPosition;
				}
			}
			lEditor->SetTarget(range);
			posFind = lEditor->SearchInTarget(findWhatText);
		}
	}
	while (findInStyle && (posFind >= 0) && (findStyle != lEditor->UnsignedStyleAt(posFind))) {
		if (range.start < range.end) {
			lEditor->SetTarget(SA::Span(posFind + 1, range.end));
		} else {
			lEditor->SetTarget(SA::Span(range.start, posFind + 1));
		}
		posFind = lEditor->SearchInTarget(findWhatText);
	}
	return posFind;
}

void SciTEBase::SetFindText(std::string_view sFind) {
	findWhat = sFind;
	props.Set("find.what", findWhat);
}

void SciTEBase::SetFind(std::string_view sFind) {
	SetFindText(sFind);
	InsertFindInMemory();
}

bool SciTEBase::FindHasText() const noexcept {
	return !findWhat.empty();
}

void SciTEBase::SetReplace(std::string_view sReplace) {
	replaceWhat = sReplace;
	memReplaces.Insert(replaceWhat);
}

void SciTEBase::SetCaretAsStart() {
	searchStartPosition = lEditor->SelectionStart();
}

void SciTEBase::MoveBack() {
	SetSelection(searchStartPosition, searchStartPosition, *lEditor);
}

void SciTEBase::ScrollEditorIfNeeded() {
	GUI::Point ptCaret;
	const SA::Position caret = lEditor->CurrentPos();
	ptCaret.x = lEditor->PointXFromPosition(caret);
	ptCaret.y = lEditor->PointYFromPosition(caret);
	ptCaret.y += lEditor->TextHeight(0) - 1;

	const GUI::Rectangle rcEditor = lEditor->GetClientPosition();
	if (!rcEditor.Contains(ptCaret))
		lEditor->ScrollCaret();
}

SA::Position SciTEBase::FindNext(bool reverseDirection, bool showWarnings, bool allowRegExp) {

	if (!isFromButton) {
		Sci_Position startSel = lEditor->SelectionStart();
		Sci_Position endSel = lEditor->SelectionEnd();
		if (startSel != endSel) {
			SelectionIntoFind();
		}
	}
	isFromButton = false;
	lEditor->CallTipCancel();

	if (findWhat.length() == 0) {
		Find();
		return -1;
	}
	const std::string findTarget = UnSlashAsNeeded(EncodeString(findWhat), unSlash, regExp);
	if (findTarget.length() == 0)
		return -1;

	const SA::Position lengthDoc = lEditor->Length();
	const SA::Span rangeSelection = lEditor->SelectionSpan();
	SA::Span rangeSearch(rangeSelection.end, lengthDoc);
	if (reverseDirection) {
		rangeSearch = SA::Span(rangeSelection.start, 0);
	}

	const bool performRegExp = regExp && allowRegExp;
	lEditor->SetSearchFlags(SearchFlags(performRegExp));
	const bool notEmptyAtStartRegEx = performRegExp && (rangeSelection.Length() == 0);
	SA::Position posFind = FindInTarget(findTarget, rangeSearch, notEmptyAtStartRegEx);
	if (posFind == -1 && wrapFind) {
		// Failed to find in indicated direction
		// so search from the beginning (forward) or from the end (reverse)
		// unless wrapFind is false
		const SA::Span rangeAll = reverseDirection ?
					   SA::Span(lengthDoc, 0) : SA::Span(0, lengthDoc);
		posFind = FindInTarget(findTarget, rangeAll, false);
		WarnUser(warnFindWrapped);
		WarnFinished("Search loop");
	}
	if (posFind < 0) {
		havefound = false;
		failedfind = true;
		if (showWarnings) {
			WarnUser(warnNotFound);
			//FindMessageBox("Can not find the string '^0'.",
			//	       &findWhat);
			WarnFinished(("Can not find the string \n\"" + findWhat + "\"").data());
		}
	} else {
		havefound = true;
		failedfind = false;
		const SA::Span rangeTarget = lEditor->TargetSpan();
		// Ensure found text is styled so that caret will be made visible but
		// only perform style in synchronous styling mode.
		const SA::Position endStyled = lEditor->EndStyled();
		if ((endStyled < rangeTarget.end) && (idleStyling == SA::IdleStyling::None)) {
			lEditor->Colourise(endStyled,
				lEditor->LineStart(lEditor->LineFromPosition(rangeTarget.end) + 1));
		}
		EnsureRangeVisible(*lEditor, rangeTarget);
		lEditor->ScrollRange(rangeTarget.start, rangeTarget.end);
		SetSelection(rangeTarget.start, rangeTarget.end, *lEditor);
		if (!replacing && (closeFind != CloseFind::closePrevent)) {
			DestroyFindReplace();
		}
	}
	return posFind;
}

void SciTEBase::WarnFinished(std::string warn) {
	Sci_Position pos = lEditor->CurrentPos();
	lEditor->CallTipShow(pos, warn.data());
}

void SciTEBase::HideMatch() {
}

void SciTEBase::ReplaceOnce(bool showWarnings) {
	if (!FindHasText())
		return;

	bool haveWarned = false;
	if (!havefound) {
		const SA::Span rangeSelection = lEditor->SelectionSpan();
		SetSelection(rangeSelection.start, rangeSelection.start, *lEditor);
		isFromButton = true;
		FindNext(false);
		haveWarned = !havefound;
	}

	if (havefound) {
		const std::string replaceTarget = UnSlashAsNeeded(EncodeString(replaceWhat), unSlash, regExp);
		const SA::Span rangeSelection = lEditor->SelectionSpan();
		lEditor->SetTarget(rangeSelection);
		SA::Position lenReplaced = replaceTarget.length();
		if (regExp)
			lenReplaced = lEditor->ReplaceTargetRE(replaceTarget);
		else	// Allow \0 in replacement
			lEditor->ReplaceTarget(replaceTarget);
		SetSelection(rangeSelection.start + lenReplaced, rangeSelection.start, *lEditor);
		SetCaretAsStart();
		havefound = false;
	}

	isFromButton = true;
	FindNext(false, showWarnings && !haveWarned);
}

intptr_t SciTEBase::DoReplaceAll(bool inSelection) {
	const std::string findTarget = UnSlashAsNeeded(EncodeString(findWhat), unSlash, regExp);
	if (findTarget.length() == 0) {
		return -1;
	}

	const SA::Span rangeSelection = lEditor->SelectionSpan();
	SA::Span rangeSearch = rangeSelection;
	const int countSelections = lEditor->Selections();
	if (inSelection) {
		const SA::SelectionMode selType = lEditor->SelectionMode();
		if (selType == SA::SelectionMode::Lines) {
			// Take care to replace in whole lines
			const SA::Line startLine = lEditor->LineFromPosition(rangeSearch.start);
			rangeSearch.start = lEditor->LineStart(startLine);
			const SA::Line endLine = lEditor->LineFromPosition(rangeSearch.end);
			rangeSearch.end = lEditor->LineStart(endLine + 1);
		} else {
			for (int i=0; i<countSelections; i++) {
				rangeSearch.start = std::min(rangeSearch.start, lEditor->SelectionNStart(i));
				rangeSearch.end = std::max(rangeSearch.end, lEditor->SelectionNEnd(i));
			}
		}
		if (rangeSearch.Length() == 0) {
			return -2;
		}
	} else {
		rangeSearch.end = LengthDocument();
		if (wrapFind) {
			// Whole document
			rangeSearch.start = 0;
		}
		// If not wrapFind, replace all only from caret to end of document
	}

	const std::string replaceTarget = UnSlashAsNeeded(EncodeString(replaceWhat), unSlash, regExp);
	lEditor->SetSearchFlags(SearchFlags(regExp));
	SA::Position posFind = FindInTarget(findTarget, rangeSearch, false);
	if ((posFind >= 0) && (posFind <= rangeSearch.end)) {
		SA::Position lastMatch = posFind;
		intptr_t replacements = 0;
		UndoBlock ub(*lEditor);
		// Replacement loop
		while (posFind >= 0) {
			const SA::Position lenTarget = lEditor->TargetEnd() - posFind;
			if (inSelection && countSelections > 1) {
				// We must check that the found target is entirely inside a selection
				bool insideASelection = false;
				for (int i=0; i<countSelections && !insideASelection; i++) {
					const SA::Position startPos = lEditor->SelectionNStart(i);
					const SA::Position endPos = lEditor->SelectionNEnd(i);
					if (posFind >= startPos && posFind + lenTarget <= endPos)
						insideASelection = true;
				}
				if (!insideASelection) {
					// Found target is totally or partly outside the selections
					lastMatch = posFind + 1;
					if (lastMatch >= rangeSearch.end) {
						// Run off the end of the document/selection with an empty match
						posFind = -1;
					} else {
						posFind = FindInTarget(findTarget, SA::Span(lastMatch, rangeSearch.end), false);
					}
					continue;	// No replacement
				}
			}
			SA::Position lenReplaced = replaceTarget.length();
			bool notEmptyAtStartRegEx = false;
			if (regExp) {
				lenReplaced = lEditor->ReplaceTargetRE(replaceTarget);
				notEmptyAtStartRegEx = lenTarget <= 0;
			} else {
				lEditor->ReplaceTarget(replaceTarget);
			}
			// Modify for change caused by replacement
			rangeSearch.end += lenReplaced - lenTarget;
			// For the special cases of start of line and end of line
			// something better could be done but there are too many special cases
			lastMatch = posFind + lenReplaced;
			if (lastMatch >= rangeSearch.end) {
				// Run off the end of the document/selection with an empty match
				posFind = -1;
			} else {
				posFind = FindInTarget(findTarget, SA::Span(lastMatch, rangeSearch.end), notEmptyAtStartRegEx);
			}
			replacements++;
		}
		if (inSelection) {
			if (countSelections == 1)
				SetSelection(rangeSearch.start, rangeSearch.end, *lEditor);
		} else {
			SetSelection(lastMatch, lastMatch, *lEditor);
		}
		return replacements;
	}
	return 0;
}

intptr_t SciTEBase::ReplaceAll(bool inSelection) {
	wEditor.SetRedraw(false);
	wEditor2.SetRedraw(false);
	const intptr_t replacements = DoReplaceAll(inSelection);
	wEditor.SetRedraw(true);
	wEditor2.SetRedraw(true);
	props.Set("Replacements", std::to_string(replacements > 0 ? replacements : 0));
	UpdateStatusBar(false);
	if (replacements == -1) {
		FindMessageBox(
			inSelection ?
			"Find string must not be empty for 'Replace in Selection' command." :
			"Find string must not be empty for 'Replace All' command.");
	} else if (replacements == -2) {
		FindMessageBox(
			"Selection must not be empty for 'Replace in Selection' command.");
	} else if (replacements == 0) {
		FindMessageBox(
			"No replacements because string '^0' was not present.", &findWhat);
	}
	return replacements;
}

intptr_t SciTEBase::ReplaceInBuffers() {
	const BufferIndex currentBuffer = buffers.Current();
	intptr_t replacements = 0;
	for (int i = 0; i < buffers.length; i++) {
		SetDocumentAt(i);
		replacements += DoReplaceAll(false);
		if (i == 0 && replacements < 0) {
			FindMessageBox(
				"Find string must not be empty for 'Replace in Buffers' command.");
			break;
		}
	}
	SetDocumentAt(currentBuffer);
	props.Set("Replacements", std::to_string(replacements));
	UpdateStatusBar(false);
	if (replacements == 0) {
		FindMessageBox(
			"No replacements because string '^0' was not present.", &findWhat);
	}
	return replacements;
}

void SciTEBase::UIClosed() {
	if (CurrentBuffer()->findMarks == Buffer::FindMarks::temporary) {
		RemoveFindMarks();
	}
}

void SciTEBase::UIHasFocus() {
}

void SciTEBase::OutputAppendString(std::string_view s) {
	wOutput.AppendText(s.length(), s.data());
	if (scrollOutput) {
		const SA::Line line = wOutput.LineCount();
		const SA::Position lineStart = wOutput.LineStart(line);
		wOutput.GotoPos(lineStart);
	}
}

void SciTEBase::OutputAppendStringSynchronised(std::string_view s) {
	// This may be called from secondary thread so always use Send instead of Call
	wOutput.Send(SCI_APPENDTEXT, s.length(), SptrFromString(s.data()));
	if (scrollOutput) {
		const SA::Line line = wOutput.Send(SCI_GETLINECOUNT);
		const SA::Position lineStart = wOutput.Send(SCI_POSITIONFROMLINE, line);
		wOutput.Send(SCI_GOTOPOS, lineStart);
	}
}

void SciTEBase::Execute() {
	props.Set("CurrentMessage", "");
	dirNameForExecute = FilePath();
	bool displayParameterDialog = false;
	parameterisedCommand = "";
	for (size_t ic = 0; ic < JobQueue::commandMax; ic++) {
		if (jobQueue.jobQueue[ic].command.starts_with("*")) {
			displayParameterDialog = true;
			jobQueue.jobQueue[ic].command.erase(0, 1);
			parameterisedCommand = jobQueue.jobQueue[ic].command;
		}
		if (jobQueue.jobQueue[ic].directory.IsSet()) {
			dirNameForExecute = jobQueue.jobQueue[ic].directory;
		}
	}
	if (displayParameterDialog) {
		if (!ParametersDialog(true)) {
			jobQueue.ClearJobs();
			return;
		}
	} else {
		ParamGrab();
	}
	for (size_t ic = 0; ic < JobQueue::commandMax; ic++) {
		if (jobQueue.jobQueue[ic].jobType != JobSubsystem::grep) {
			jobQueue.jobQueue[ic].command = props.Expand(jobQueue.jobQueue[ic].command);
		}
	}

	if (jobQueue.ClearBeforeExecute()) {
		wOutput.ClearAll();
	}

	wOutput.MarkerDeleteAll(-1);
	wEditor.MarkerDeleteAll(0);
	wEditor2.MarkerDeleteAll(0);
	// Ensure the output pane is visible
	if (jobQueue.ShowOutputPane()) {
		SetOutputVisibility(true);
	}

	jobQueue.SetCancelFlag(false);
	if (jobQueue.HasCommandToRun()) {
		jobQueue.SetExecuting(true);
	}
	CheckMenus();
	dirNameAtExecute = filePath.Directory();
}

void SciTEBase::SetOutputVisibility(bool show) {
	if (show) {
		if (heightOutput <= heightBar) {
			if (previousHeightOutput < minimumSplit) {
				heightOutput = NormaliseSplit(splitVertical ? baseSplitHorizontal : baseSplitVertical);
				previousHeightOutput = heightOutput;
			} else {
				heightOutput = NormaliseSplit(previousHeightOutput);
			}
		}
	} else {
		if (heightOutput > heightBar) {
			heightOutput = NormaliseSplit(0);
			WindowSetFocus(*lEditor);
		}
	}
	heightEditorSplit = NormaliseESplit(heightEditorSplit);
	SizeSubWindows();
	Redraw();
}

// Background threads that are send text to the output pane want it to be made visible.
// Derived methods for each platform may perform thread synchronization.
void SciTEBase::ShowOutputOnMainThread() {
	SetOutputVisibility(true);
}

void SciTEBase::ToggleOutputVisible() {
	SetOutputVisibility(heightOutput <= heightBar);
}

void SciTEBase::ToggleEditor2Visible() {
	SetEditor2Visibility(heightEditorSplit <= heightBar);
}

void SciTEBase::SetEditor2Visibility(bool split) {
	if (split) {
		const GUI::Rectangle rcInternal = wContent.GetClientPosition();
		const int h = rcInternal.Height();
		heightEditorSplit = h/3;
	}
	else {
		heightEditorSplit = 0;
	}
	SizeContentWindows();
}

void SciTEBase::BookmarkAdd(SA::Line lineno, int mark) {
	if (lineno == -1)
		lineno = GetCurrentLineNumber();
	if (!BookmarkPresent(lineno, mark))
		wEditor.MarkerAdd(lineno, mark);
}

void SciTEBase::BookmarkDelete(SA::Line lineno, int mark) {
	if (lineno == -1)
		lineno = GetCurrentLineNumber();
	if (BookmarkPresent(lineno, mark))
		wEditor.MarkerDelete(lineno, mark);
}

bool SciTEBase::BookmarkPresent(SA::Line lineno, int mark) {
	if (lineno == -1)
		lineno = GetCurrentLineNumber();
	const int state = wEditor.MarkerGet(lineno);
	return state & (1 << mark);
}

void SciTEBase::BookmarkToggle(SA::Line lineno) {
	if (lineno == -1)
		lineno = GetCurrentLineNumber();

	if (BookmarkPresent(lineno, markerUserBookmark)) {
		while (BookmarkPresent(lineno, markerUserBookmark)) {
			BookmarkDelete(lineno, markerUserBookmark);
		}
		BookmarkAdd(lineno, markerBookmark);
		return;
	}
	else if (BookmarkPresent(lineno, markerBookmark)) {
		while (BookmarkPresent(lineno, markerBookmark)) {
			BookmarkDelete(lineno, markerBookmark);
		}
		return;
	} else {
		BookmarkAdd(lineno, markerUserBookmark);
	}
}

void SciTEBase::BookmarkNext(bool forwardScan, bool select) {
	const SA::Line lineno = GetCurrentLineNumber();
	SA::Message sciMarker = SA::Message::MarkerNext;
	SA::Line lineStart = lineno + 1;	//Scan starting from next line
	SA::Line lineRetry = 0;				//If not found, try from the beginning
	const SA::Position anchor = lEditor->Anchor();
	if (!forwardScan) {
		lineStart = lineno - 1;		//Scan starting from previous line
		lineRetry = lEditor->LineCount();	//If not found, try from the end
		sciMarker = SA::Message::MarkerPrevious;
	}
	constexpr unsigned int maskBookmark = 1 << markerBookmark;
	SA::Line nextLine = lEditor->Call(sciMarker, lineStart, maskBookmark);
	if (nextLine < 0)
		nextLine = lEditor->Call(sciMarker, lineRetry, maskBookmark);
	if (nextLine < 0 || nextLine == lineno)	// No bookmark (of the given type) or only one, and already on it
		WarnUser(warnNoOtherBookmark);
	else {
		GotoLineEnsureVisible(nextLine);
		if (select) {
			lEditor->SetAnchor(anchor);
		}
	}
}

void SciTEBase::BookmarkSelectAll() {
	std::vector<SA::Line> bookmarks;
	SA::Line lineBookmark = -1;
	while ((lineBookmark = lEditor->MarkerNext(lineBookmark + 1, 1 << markerBookmark)) >= 0) {
		bookmarks.push_back(lineBookmark);
	}
	for (size_t i = 0; i < bookmarks.size(); i++) {
		const SA::Span range = {
			lEditor->LineStart(bookmarks[i]),
			lEditor->LineStart(bookmarks[i] + 1)
		};
		if (i == 0) {
			lEditor->SetSelection(range.end, range.start);
		} else {
			lEditor->AddSelection(range.end, range.start);
		}
	}
}

GUI::Rectangle SciTEBase::GetClientRectangle() {
	return wContent.GetClientPosition();
}

void SciTEBase::Redraw() {
	wSciTE.InvalidateAll();
	wEditor.InvalidateAll();
	wEditor2.InvalidateAll();
	wOutput.InvalidateAll();
	wMarkerMap.InvalidateAll();
}

StringVector SciTEBase::GetNearestWords(const char *wordStart, size_t searchLen,
				       const char *separators, bool ignoreCase /*=false*/, bool exactLen /*=false*/) {
	StringVector words;
	while (words.empty() && *separators) {
		words = apis.GetNearestWords(wordStart, searchLen, ignoreCase, *separators, exactLen);
		separators++;
	}
	return words;
}

void SciTEBase::FillFunctionDefinition(SA::Position pos /*= -1*/) {
	if (pos > 0) {
		lastPosCallTip = pos;
	}
	if (apis) {
		StringVector words = GetNearestWords(currentCallTipWord.c_str(), currentCallTipWord.length(),
						    calltipParametersStart.c_str(), callTipIgnoreCase, true);
		if (words.empty())
			return;
		// Counts how many call tips
		maxCallTips = words.size();

		// Should get current api definition
		std::string word = apis.GetNearestWord(currentCallTipWord.c_str(), currentCallTipWord.length(),
						       callTipIgnoreCase, calltipWordCharacters, currentCallTip);
		if (word.length()) {
			functionDefinition = word;
			if (maxCallTips > 1) {
				functionDefinition.insert(0, "\001");
			}

			if (calltipEndDefinition != "") {
				const size_t posEndDef = functionDefinition.find(calltipEndDefinition);
				if (maxCallTips > 1) {
					if (posEndDef != std::string::npos) {
						functionDefinition.insert(posEndDef + calltipEndDefinition.length(), "\n\002");
					} else {
						functionDefinition.append("\n\002");
					}
				} else {
					if (posEndDef != std::string::npos) {
						functionDefinition.insert(posEndDef + calltipEndDefinition.length(), "\n");
					}
				}
			} else if (maxCallTips > 1) {
				functionDefinition.insert(1, "\002");
			}

			std::string definitionForDisplay;
			if (callTipUseEscapes) {
				definitionForDisplay = UnSlashString(functionDefinition);
			} else {
				definitionForDisplay = functionDefinition;
			}

			lEditor->CallTipShow(lastPosCallTip - currentCallTipWord.length(), definitionForDisplay.c_str());
			ContinueCallTip();
		}
	}
}

bool SciTEBase::StartCallTip() {
	currentCallTip = 0;
	currentCallTipWord = "";
	std::string line = GetCurrentLine();
	SA::Position current = GetCaretInLine();
	SA::Position pos = lEditor->CurrentPos();
	do {
		int braces = 0;
		while (current > 0 && (braces || !Contains(calltipParametersStart, line[current - 1]))) {
			if (Contains(calltipParametersStart, line[current - 1]))
				braces--;
			else if (Contains(calltipParametersEnd, line[current - 1]))
				braces++;
			current--;
			pos--;
		}
		if (current > 0) {
			current--;
			pos--;
		} else
			break;
		while (current > 0 && IsASpace(line[current - 1])) {
			current--;
			pos--;
		}
	} while (current > 0 && !Contains(calltipWordCharacters, line[current - 1]));
	if (current <= 0)
		return true;

	startCalltipWord = current - 1;
	while (startCalltipWord > 0 &&
			Contains(calltipWordCharacters, line[startCalltipWord - 1])) {
		startCalltipWord--;
	}

	line.at(current) = '\0';
	currentCallTipWord = line.c_str() + startCalltipWord;
	functionDefinition = "";
	FillFunctionDefinition(pos);
	return true;
}

void SciTEBase::ContinueCallTip() {
	std::string line = GetCurrentLine();
	const SA::Position current = GetCaretInLine();

	int braces = 0;
	int commas = 0;
	for (SA::Position i = startCalltipWord; i < current; i++) {
		if (Contains(calltipParametersStart, line[i]))
			braces++;
		else if (Contains(calltipParametersEnd, line[i]) && braces > 0)
			braces--;
		else if (braces == 1 && Contains(calltipParametersSeparators, line[i]))
			commas++;
	}

	size_t startHighlight = 0;
	while ((startHighlight < functionDefinition.length()) && !Contains(calltipParametersStart, functionDefinition[startHighlight]))
		startHighlight++;
	if ((startHighlight < functionDefinition.length()) && Contains(calltipParametersStart, functionDefinition[startHighlight]))
		startHighlight++;
	while ((startHighlight < functionDefinition.length()) && commas > 0) {
		if (Contains(calltipParametersSeparators, functionDefinition[startHighlight]))
			commas--;
		// If it reached the end of the argument list it means that the user typed in more
		// arguments than the ones listed in the calltip
		if (Contains(calltipParametersEnd, functionDefinition[startHighlight]))
			commas = 0;
		else
			startHighlight++;
	}
	if ((startHighlight < functionDefinition.length()) && Contains(calltipParametersSeparators, functionDefinition[startHighlight]))
		startHighlight++;
	size_t endHighlight = startHighlight;
	while ((endHighlight < functionDefinition.length()) && !Contains(calltipParametersSeparators, functionDefinition[endHighlight]) && !Contains(calltipParametersEnd, functionDefinition[endHighlight]))
		endHighlight++;
	if (callTipUseEscapes) {
		const std::string sPreHighlight = UnSlashString(functionDefinition.substr(0, startHighlight));
		const size_t unslashedStartHighlight = sPreHighlight.length();

		size_t unslashedEndHighlight = unslashedStartHighlight;
		if (startHighlight < endHighlight) {
			const std::string sHighlight = UnSlashString(
				functionDefinition.substr(startHighlight, endHighlight - startHighlight));
			unslashedEndHighlight = unslashedStartHighlight + sHighlight.length();
		}

		startHighlight = unslashedStartHighlight;
		endHighlight = unslashedEndHighlight;
	}

	lEditor->CallTipSetHlt(startHighlight, endHighlight);
}

namespace {

std::string EliminateDuplicateWords(const StringVector &words) {
	std::set<std::string> wordSet;
	std::string wordsOut;

	for (const std::string &word : words) {
		std::pair<std::set<std::string>::iterator, bool> result = wordSet.insert(word);
		if (result.second) {
			if (!wordsOut.empty())
				wordsOut += ' ';
			wordsOut += word;
		}
	}
	return wordsOut;
}

}

bool SciTEBase::StartAutoComplete() {
	const std::string line = GetCurrentLine();
	const SA::Position current = GetCaretInLine();

	SA::Position startword = current;

	while ((startword > 0) &&
			(Contains(calltipWordCharacters, line[startword - 1]) ||
			 Contains(autoCompleteStartCharacters, line[startword - 1]))) {
		startword--;
	}

	const std::string root = line.substr(startword, current - startword);
	if (apis) {
		const StringVector words = GetNearestWords(root.c_str(), root.length(),
						    calltipParametersStart.c_str(), autoCompleteIgnoreCase);
		if (!words.empty()) {
			std::string wordsUnique = EliminateDuplicateWords(words);
			lEditor->AutoCSetSeparator(' ');
			lEditor->AutoCSetMaxHeight(autoCompleteVisibleItemCount);
			lEditor->AutoCShow(root.length(), wordsUnique.c_str());
		}
	}
	return true;
}

bool SciTEBase::StartAutoCompleteWord(bool onlyOneWord) {
	const std::string line = GetCurrentLine();
	const SA::Position current = GetCaretInLine();

	SA::Position startword = current;
	// Autocompletion of pure numbers is mostly an annoyance
	bool allNumber = true;
	while (startword > 0 && Contains(wordCharacters, line[startword - 1])) {
		startword--;
		if (line[startword] < '0' || line[startword] > '9') {
			allNumber = false;
		}
	}
	if (startword == current || allNumber)
		return true;
	const std::string root = line.substr(startword, current - startword);
	const SA::Position rootLength = root.length();
	const SA::Position doclen = LengthDocument();
	const SA::FindOption flags =
		SA::FindOption::WordStart | (autoCompleteIgnoreCase ? SA::FindOption::None : SA::FindOption::MatchCase);
	const SA::Position posCurrentWord = lEditor->CurrentPos() - rootLength;

	// wordList contains a list of words to display in an autocompletion list.
	AutoCompleteWordList wordList;

	lEditor->SetTarget(SA::Span(0, doclen));
	lEditor->SetSearchFlags(flags);
	SA::Position posFind = lEditor->SearchInTarget(root);
	TextReader acc(*lEditor);
	while (posFind >= 0 && posFind < doclen) {	// search all the document
		SA::Position wordEnd = posFind + rootLength;
		if (posFind != posCurrentWord) {
			while (Contains(wordCharacters, acc.SafeGetCharAt(wordEnd)))
				wordEnd++;
			const SA::Position wordLength = wordEnd - posFind;
			if (wordLength > rootLength) {
				const std::string word = lEditor->StringOfRange(SA::Span(posFind, wordEnd));
				if (wordList.Add(word)) {
					if (onlyOneWord && wordList.Count() > 1) {
						return true;
					}
				}
			}
		}
		lEditor->SetTarget(SA::Span(wordEnd, doclen));
		posFind = lEditor->SearchInTarget(root);
	}
	if ((wordList.Count() != 0) && (!onlyOneWord || (wordList.MinWordLength() > static_cast<size_t>(rootLength)))) {
		const std::string wordsNear = wordList.Sorted(autoCompleteIgnoreCase);
		lEditor->AutoCSetSeparator('\n');
		lEditor->AutoCSetMaxHeight(autoCompleteVisibleItemCount);
		lEditor->AutoCShow(rootLength, wordsNear.c_str());
	} else {
		lEditor->AutoCCancel();
	}
	return true;
}

bool SciTEBase::PerformInsertAbbreviation() {
	const std::string data = propsAbbrev.GetString(abbrevInsert);
	if (data.empty()) {
		return true; // returning if expanded abbreviation is empty
	}

	const std::string expbuf = UnSlashString(data);
	const size_t expbuflen = expbuf.length();

	const SA::Position selStart = lEditor->SelectionStart();
	SA::Position selLength = lEditor->SelectionEnd() - selStart;
	SA::Position selCollapse = -1;
	SA::Position caretPos = -1; // caret position
	SA::Line currentLineNumber = lEditor->LineFromPosition(selStart);
	int indent = 0;
	const int indentSize = lEditor->Indent();
	const int indentChars = lEditor->UseTabs() ? lEditor->TabWidth() : 1;
	int indentExtra = 0;
	bool isIndent = true;
	const SA::EndOfLine eolMode = lEditor->EOLMode();

	UndoBlock ub(*lEditor);

	// add temporary characters around the selection for correct line indentation
	// if there are tabs or spaces at the beginning or end of the selection
	lEditor->InsertText(selStart, "|");
	selLength++;
	lEditor->InsertText(selStart + selLength, "|");
	if (props.GetInt("indent.automatic")) {
		indent = GetLineIndentation(currentLineNumber);
	}

	lEditor->GotoPos(selStart);

	size_t lastPipe = expbuflen; // position of last '|'
	for (size_t i = 0; i < expbuflen; i++) {
		if (expbuf[i] == '|') {
			if (i < (expbuflen - 1) && expbuf[i + 1] == '|') {
				i++;
			} else {
				lastPipe = i;
			}
		}
	}

	// add the abbreviation one character at a time
	for (size_t i = 0; i < expbuflen; i++) {
		const char c = expbuf[i];
		if (isIndent && c == '\t') {
			SetLineIndentation(currentLineNumber, GetLineIndentation(currentLineNumber) + indentSize);
			indentExtra += indentSize;
		} else {
			std::string abbrevText;
			switch (c) {
			case '|':
				// user may want to insert '|' instead of caret
				if (i < (expbuflen - 1) && expbuf[i + 1] == '|') {
					// put '|' into the line
					abbrevText += c;
					i++;
				} else if (i != lastPipe) {
					if (selCollapse == -1) {
						selCollapse = lEditor->CurrentPos();
					}
				} else if (caretPos == -1) {
					caretPos = lEditor->CurrentPos();

					// indent on multiple lines
					SA::Line j = currentLineNumber + 1; // first line indented as others
					currentLineNumber = lEditor->LineFromPosition(caretPos + selLength);
					for (; j <= currentLineNumber; j++) {
						SetLineIndentation(j, GetLineIndentation(j) + indentExtra);
						selLength += indentExtra / indentChars;
					}

					lEditor->GotoPos(caretPos + selLength);
				}
				break;
			case '\n':
				abbrevText += LineEndString(eolMode);
				break;
			default:
				abbrevText += c;
				break;
			}
			lEditor->ReplaceSel(abbrevText.c_str());
			if (c == '\n') {
				isIndent = true;
				indentExtra = 0;
				currentLineNumber++;
				SetLineIndentation(currentLineNumber, indent);
			} else {
				isIndent = false;
			}
		}
	}

	// make sure the caret is set before the last temporary character and remove it
	if (caretPos == -1) {
		caretPos = lEditor->CurrentPos();
		lEditor->GotoPos(caretPos + selLength);
	}
	lEditor->DeleteRange(lEditor->CurrentPos(), 1);

	// set the caret before the first temporary character and remove it
	lEditor->GotoPos(caretPos);
	lEditor->DeleteRange(lEditor->CurrentPos(), 1);
	selLength--;

	// restore selection
	if (selCollapse == -1) {
		lEditor->SetSelectionEnd(caretPos + selLength);
	} else {
		lEditor->SetEmptySelection(selCollapse);
	}

	return true;
}

bool SciTEBase::StartExpandAbbreviation() {
	const SA::Position currentPos = GetCaretInLine();
	const SA::Position position = lEditor->CurrentPos(); // from the beginning
	const std::string linebuf(GetCurrentLine(), 0, currentPos);	// Just get text to the left of the caret
	const SA::Position abbrevPos = (currentPos > 32 ? currentPos - 32 : 0);
	const char *abbrev = linebuf.c_str() + abbrevPos;
	std::string data;
	SA::Position abbrevLength = currentPos - abbrevPos;
	// Try each potential abbreviation from the first letter on a line
	// and expanding to the right.
	// We arbitrarily limit the length of an abbreviation (seems a reasonable value..),
	// and of course stop on the caret.
	while (abbrevLength > 0) {
		data = propsAbbrev.GetString(abbrev);
		if (!data.empty()) {
			break;	/* Found */
		}
		abbrev++;	// One more letter to the right
		abbrevLength--;
	}

	if (data.empty()) {
		WarnUser(warnNotFound);	// No need for a special warning
		return true; // returning if expanded abbreviation is empty
	}

	const std::string expbuf = UnSlashString(data);
	const size_t expbuflen = expbuf.length();

	SA::Position caretPos = -1; // caret position
	SA::Line currentLineNumber = GetCurrentLineNumber();
	int indent = 0;
	const int indentSize = lEditor->Indent();
	bool isIndent = true;
	const SA::EndOfLine eolMode = lEditor->EOLMode();

	UndoBlock ub(*lEditor);

	// add a temporary character for correct line indentation
	// if there are tabs or spaces after the caret
	lEditor->InsertText(position, "|");
	if (props.GetInt("indent.automatic")) {
		indent = GetLineIndentation(currentLineNumber);
	}

	lEditor->SetSel(position - abbrevLength, position);

	// add the abbreviation one character at a time
	for (size_t i = 0; i < expbuflen; i++) {
		const char c = expbuf[i];
		if (isIndent && c == '\t') {
			SetLineIndentation(currentLineNumber, GetLineIndentation(currentLineNumber) + indentSize);
		} else {
			std::string abbrevText;
			switch (c) {
			case '|':
				// user may want to insert '|' instead of caret
				if (i < (expbuflen - 1) && expbuf[i + 1] == '|') {
					// put '|' into the line
					abbrevText += c;
					i++;
				} else if (caretPos == -1) {
					if (i == 0) {
						// when caret is set at the first place in abbreviation
						caretPos = lEditor->CurrentPos() - abbrevLength;
					} else {
						caretPos = lEditor->CurrentPos();
					}
				}
				break;
			case '\n':
				abbrevText += LineEndString(eolMode);
				break;
			default:
				abbrevText += c;
				break;
			}
			lEditor->ReplaceSel(abbrevText.c_str());
			if (c == '\n') {
				isIndent = true;
				currentLineNumber++;
				SetLineIndentation(currentLineNumber, indent);
			} else {
				isIndent = false;
			}
		}
	}

	// remove the temporary character
	lEditor->DeleteRange(lEditor->CurrentPos(), 1);

	// set the caret to the desired position
	if (caretPos != -1) {
		lEditor->GotoPos(caretPos);
	}

	return true;
}

bool SciTEBase::StartBlockComment() {
	std::string fileNameForExtension = ExtensionFileName();
	std::string lexerName = props.GetNewExpandString("lexer.", fileNameForExtension);
	std::string base("comment.block.");
	std::string commentAtLineStart("comment.block.at.line.start.");
	base += lexerName;
	commentAtLineStart += lexerName;
	const bool placeCommentsAtLineStart = props.GetInt(commentAtLineStart) != 0;

	std::string comment = props.GetString(base);
	if (comment == "") { // user friendly error message box
		GUI::gui_string sBase = GUI::StringFromUTF8(base);
		GUI::gui_string error = LocaliseMessage(
						"Block comment variable '^0' is not defined in SciTE *.properties!", sBase.c_str());
		WindowMessageBox(wSciTE, error);
		return true;
	}
	const std::string longComment = comment;
	const SA::Position longCommentLength = longComment.length();
	SA::Position selectionStart = lEditor->SelectionStart();
	SA::Position selectionEnd = lEditor->SelectionEnd();
	const SA::Position caretPosition = lEditor->CurrentPos();
	// checking if caret is located in _beginning_ of selected block
	const bool moveCaret = caretPosition < selectionEnd;
	const SA::Line selStartLine = lEditor->LineFromPosition(selectionStart);
	SA::Line selEndLine = lEditor->LineFromPosition(selectionEnd);
	const SA::Line lines = selEndLine - selStartLine;
	const SA::Position firstSelLineStart = lEditor->LineStart(selStartLine);
	// "caret return" is part of the last selected line
	if ((lines > 0) &&
			(selectionEnd == lEditor->LineStart(selEndLine)))
		selEndLine--;
	UndoBlock ub(*lEditor);
	bool getcommentall = true;
	bool commentall = false;
	for (SA::Line i = selStartLine; i <= selEndLine; i++) {
		const SA::Position lineStart = lEditor->LineStart(i);
		SA::Position lineIndent = lineStart;
		const SA::Position lineEnd = lEditor->LineEnd(i);
		if (!placeCommentsAtLineStart) {
			lineIndent = GetLineIndentPosition(i);
		}
		std::string linebuf = lEditor->StringOfRange(SA::Span(lineIndent, lineEnd));

		// empty lines are not commented
		if (linebuf.length() < 1)
			continue;
		if (getcommentall) {
			getcommentall = false;
			commentall = linebuf.starts_with(comment);
		}
		if (commentall) {
			SA::Position commentLength = comment.length();
			if (linebuf.starts_with(longComment)) {
				// Removing comment with space after it.
				commentLength = longCommentLength;
			}
			lEditor->SetSel(lineIndent, lineIndent + commentLength);
			if (linebuf.starts_with(comment))
				lEditor->ReplaceSel("");
			if (i == selStartLine) // is this the first selected line?
				selectionStart -= commentLength;
			selectionEnd -= commentLength; // every iteration
			continue;
		}
		if (i == selStartLine) // is this the first selected line?
			selectionStart += longCommentLength;
		selectionEnd += longCommentLength; // every iteration
		lEditor->InsertText(lineIndent, longComment.c_str());
	}
	// after uncommenting selection may promote itself to the lines
	// before the first initially selected line;
	// another problem - if only comment symbol was selected;
	if (selectionStart < firstSelLineStart) {
		if (selectionStart >= selectionEnd - (longCommentLength - 1))
			selectionEnd = firstSelLineStart;
		selectionStart = firstSelLineStart;
	}
	if (moveCaret) {
		// moving caret to the beginning of selected block
		lEditor->GotoPos(selectionEnd);
		lEditor->SetCurrentPos(selectionStart);
	} else {
		lEditor->SetSel(selectionStart, selectionEnd);
	}
	return true;
}

const char *LineEndString(SA::EndOfLine eolMode) noexcept {
	switch (eolMode) {
	case SA::EndOfLine::CrLf:
		return "\r\n";
	case SA::EndOfLine::Cr:
		return "\r";
	case SA::EndOfLine::Lf:
	default:
		return "\n";
	}
}

bool SciTEBase::StartBoxComment() {
	// Get start/middle/end comment strings from options file(s)
	std::string fileNameForExtension = ExtensionFileName();
	std::string lexerName = props.GetNewExpandString("lexer.", fileNameForExtension);
	std::string startBase("comment.box.start.");
	std::string middleBase("comment.box.middle.");
	std::string endBase("comment.box.end.");
	const std::string whiteSpace(" ");
	const std::string eol(LineEndString(lEditor->EOLMode()));
	startBase += lexerName;
	middleBase += lexerName;
	endBase += lexerName;
	std::string startComment = props.GetString(startBase);
	std::string middleComment = props.GetString(middleBase);
	std::string endComment = props.GetString(endBase);
	if (startComment == "" || middleComment == "" || endComment == "") {
		GUI::gui_string sStart = GUI::StringFromUTF8(startBase);
		GUI::gui_string sMiddle = GUI::StringFromUTF8(middleBase);
		GUI::gui_string sEnd = GUI::StringFromUTF8(endBase);
		GUI::gui_string error = LocaliseMessage(
						"Box comment variables '^0', '^1' and '^2' are not defined in SciTE *.properties!",
						sStart.c_str(), sMiddle.c_str(), sEnd.c_str());
		WindowMessageBox(wSciTE, error);
		return true;
	}

	// Note selection and cursor location so that we can reselect text and reposition cursor after we insert comment strings
	SA::Position selectionStart = lEditor->SelectionStart();
	SA::Position selectionEnd = lEditor->SelectionEnd();
	const SA::Position caretPosition = lEditor->CurrentPos();
	const bool moveCaret = caretPosition < selectionEnd;
	const SA::Line selStartLine = lEditor->LineFromPosition(selectionStart);
	SA::Line selEndLine = lEditor->LineFromPosition(selectionEnd);
	SA::Line lines = selEndLine - selStartLine + 1;

	// If selection ends at start of last selected line, fake it so that selection goes to end of second-last selected line
	if (lines > 1 && selectionEnd == lEditor->LineStart(selEndLine)) {
		selEndLine--;
		lines--;
		selectionEnd = lEditor->LineEnd(selEndLine);
	}

	// Pad comment strings with appropriate whitespace, then figure out their lengths (endComment is a bit special-- see below)
	startComment += whiteSpace;
	middleComment += whiteSpace;
	const SA::Position startCommentLength = startComment.length();
	const SA::Position middleCommentLength = middleComment.length();
	const SA::Position endCommentLength = endComment.length();

	UndoBlock ub(*lEditor);

	// Insert startComment if needed
	SA::Position lineStart = lEditor->LineStart(selStartLine);
	std::string tempString = lEditor->StringOfRange(SA::Span(lineStart, lineStart + startCommentLength));
	if (startComment != tempString) {
		lEditor->InsertText(lineStart, startComment.c_str());
		selectionStart += startCommentLength;
		selectionEnd += startCommentLength;
	}

	if (lines <= 1) {
		// Only a single line was selected, so just append whitespace + end-comment at end of line if needed
		const SA::Position lineEnd = lEditor->LineEnd(selEndLine);
		tempString = lEditor->StringOfRange(SA::Span(lineEnd - endCommentLength, lineEnd));
		if (endComment != tempString) {
			endComment.insert(0, whiteSpace);
			lEditor->InsertText(lineEnd, endComment.c_str());
		}
	} else {
		// More than one line selected, so insert middleComments where needed
		for (SA::Line i = selStartLine + 1; i < selEndLine; i++) {
			lineStart = lEditor->LineStart(i);
			tempString = lEditor->StringOfRange(SA::Span(lineStart, lineStart + middleCommentLength));
			if (middleComment != tempString) {
				lEditor->InsertText(lineStart, middleComment.c_str());
				selectionEnd += middleCommentLength;
			}
		}

		// If last selected line is not middle-comment or end-comment, we need to insert
		// a middle-comment at the start of last selected line and possibly still insert
		// and end-comment tag after the last line (extra logic is necessary to
		// deal with the case that user selected the end-comment tag)
		lineStart = lEditor->LineStart(selEndLine);
		tempString = lEditor->StringOfRange(SA::Span(lineStart, lineStart + endCommentLength));
		if (endComment != tempString) {
			tempString = lEditor->StringOfRange(SA::Span(lineStart, lineStart + middleCommentLength));
			if (middleComment != tempString) {
				lEditor->InsertText(lineStart, middleComment.c_str());
				selectionEnd += middleCommentLength;
			}

			// And since we didn't find the end-comment string yet, we need to check the *next* line
			//  to see if it's necessary to insert an end-comment string and a linefeed there....
			lineStart = lEditor->LineStart(selEndLine + 1);
			tempString = lEditor->StringOfRange(SA::Span(lineStart, lineStart + endCommentLength));
			if (endComment != tempString) {
				endComment += eol;
				lEditor->InsertText(lineStart, endComment.c_str());
			}
		}
	}

	if (moveCaret) {
		// moving caret to the beginning of selected block
		lEditor->GotoPos(selectionEnd);
		lEditor->SetCurrentPos(selectionStart);
	} else {
		lEditor->SetSel(selectionStart, selectionEnd);
	}

	return true;
}

bool SciTEBase::StartStreamComment() {
	std::string fileNameForExtension = ExtensionFileName();
	const std::string lexerName = props.GetNewExpandString("lexer.", fileNameForExtension);
	std::string startBase("comment.stream.start.");
	std::string endBase("comment.stream.end.");
	std::string whiteSpace(" ");
	startBase += lexerName;
	endBase += lexerName;
	std::string startComment = props.GetString(startBase);
	std::string endComment = props.GetString(endBase);
	if (startComment == "" || endComment == "") {
		GUI::gui_string sStart = GUI::StringFromUTF8(startBase);
		GUI::gui_string sEnd = GUI::StringFromUTF8(endBase);
		GUI::gui_string error = LocaliseMessage(
						"Stream comment variables '^0' and '^1' are not defined in SciTE *.properties!",
						sStart.c_str(), sEnd.c_str());
		WindowMessageBox(wSciTE, error);
		return true;
	}
	startComment += whiteSpace;
	whiteSpace += endComment;
	endComment = whiteSpace;
	const SA::Position startCommentLength = startComment.length();
	SA::Span selection = lEditor->SelectionSpan();
	const SA::Position caretPosition = lEditor->CurrentPos();
	// checking if caret is located in _beginning_ of selected block
	const bool moveCaret = caretPosition < selection.end;
	// if there is no selection?
	if (selection.start == selection.end) {
		RangeExtend(*lEditor, selection,
			    &SciTEBase::islexerwordcharforsel);
		if (selection.start == selection.end)
			return true; // caret is located _between_ words
	}
	UndoBlock ub(*lEditor);
	lEditor->InsertText(selection.start, startComment.c_str());
	selection.end += startCommentLength;
	selection.start += startCommentLength;
	lEditor->InsertText(selection.end, endComment.c_str());
	if (moveCaret) {
		// moving caret to the beginning of selected block
		lEditor->GotoPos(selection.end);
		lEditor->SetCurrentPos(selection.start);
	} else {
		lEditor->SetSel(selection.start, selection.end);
	}
	return true;
}

/**
 * Return the length of the given line, not counting the EOL.
 */
SA::Position SciTEBase::GetLineLength(SA::Line line) {
	return lEditor->LineEnd(line) - lEditor->LineStart(line);
}

SA::Line SciTEBase::GetCurrentLineNumber() {
	return lEditor->LineFromPosition(
		lEditor->CurrentPos());
}

SA::Position SciTEBase::GetCurrentColumnNumber() {
	const int mainSel = lEditor->MainSelection();
	return lEditor->Column(lEditor->SelectionNCaret(mainSel)) +
		lEditor->SelectionNCaretVirtualSpace(mainSel);
}

ScrollDocWithOffset SciTEBase::GetCurrentScrollPosition(GUI::ScintillaWindow &wEditor) {
	const SA::Line lineDisplayTop = wEditor.FirstVisibleLine();
	const SA::Line lineDocTop = wEditor.DocLineFromVisible(lineDisplayTop);
	const SA::Line subLineTop = lineDisplayTop - wEditor.VisibleFromDocLine(lineDocTop);
	return { lineDocTop, subLineTop };
}

/**
 * Set up properties for ReadOnly, EOLMode, BufferLength, NbOfLines, SelLength, SelHeight.
 */
void SciTEBase::SetTextProperties(
	PropSetFile &ps) {			///< Property set to update.

	std::string ro = GUI::UTF8FromString(localiser.Text("READ"));
	ps.Set("ReadOnly", CurrentBuffer()->isReadOnly ? ro.c_str() : "");

	const SA::EndOfLine eolMode = lEditor->EOLMode();
	ps.Set("EOLMode", eolMode == SA::EndOfLine::CrLf ? "CR+LF" : (eolMode == SA::EndOfLine::Lf ? "LF" : "CR"));

	ps.Set("BufferLength", std::to_string(LengthDocument()));

	ps.Set("NbOfLines", std::to_string(lEditor->LineCount()));

	const SA::Span range = lEditor->SelectionSpan();
	const SA::Line selFirstLine = lEditor->LineFromPosition(range.start);
	const SA::Line selLastLine = lEditor->LineFromPosition(range.end);
	SA::Position charCount = 0;
	if (lEditor->SelectionMode() == SA::SelectionMode::Rectangle) {
		for (SA::Line line = selFirstLine; line <= selLastLine; line++) {
			const SA::Position startPos = lEditor->GetLineSelStartPosition(line);
			const SA::Position endPos = lEditor->GetLineSelEndPosition(line);
			charCount += lEditor->CountCharacters(startPos, endPos);
		}
	} else {
		charCount = lEditor->CountCharacters(range.start, range.end);
	}
	ps.Set("SelLength", std::to_string(charCount));
	const SA::Position caretPos = lEditor->CurrentPos();
	const SA::Position selAnchor = lEditor->Anchor();
	SA::Line selHeight = selLastLine - selFirstLine + 1;
	if (0 == range.Length()) {
		selHeight = 0;
	} else if (selLastLine == selFirstLine) {
		selHeight = 1;
	} else if ((lEditor->Column(caretPos) == 0 && (selAnchor <= caretPos)) ||
			((lEditor->Column(selAnchor) == 0) && (selAnchor > caretPos))) {
		selHeight = selLastLine - selFirstLine;
	}
	ps.Set("SelHeight", std::to_string(selHeight));

	props.Set("SelectionStart", std::to_string(range.start));
	props.Set("SelectionEnd", std::to_string(range.end));
}

void SciTEBase::UpdateStatusBar(bool bUpdateSlowData) {
	if (sbVisible) {
		if (bUpdateSlowData) {
			SetFileProperties(propsStatus);
		}
		SetTextProperties(propsStatus);
		propsStatus.Set("LineNumber", std::to_string(GetCurrentLineNumber() + 1));
		propsStatus.Set("ColumnNumber", std::to_string(GetCurrentColumnNumber() + 1));
		propsStatus.Set("OverType", lEditor->Overtype() ? "OVR" : "INS");
		propsStatus.Set("ZoomFactor", std::to_string(lEditor->Zoom()));

		UniMode CMode = CurrentBuffer()->unicodeMode;
		std::string cpName;
		switch (CMode) {
		case UniMode::uni8Bit: cpName = props.GetString("code.page"); break;
		case UniMode::uni16BE: cpName = "UTF16BE"; break;
		case UniMode::uni16LE: cpName = "UTF16LE"; break;
		case UniMode::utf8:    cpName = "UTF8BOM"; break;
		case UniMode::cookie:  cpName = "UTF8"; break;
		default:               cpName = "Unknown";
		}
		propsStatus.Set("CurrentCodePage", cpName.c_str());
		propsStatus.Set("CurrentCharacterSet", std::to_string(static_cast<int>(characterSet)));

		const std::string sbKey = "statusbar.text." + std::to_string(sbNum);
		std::string msg = propsStatus.GetExpandedString(sbKey);
		if (msg.size() && sbValue != msg) {	// To avoid flickering, update only if needed
			SetStatusBarText(msg.c_str());
			sbValue = msg;
		}
	} else {
		sbValue = "";
	}
}

void SciTEBase::SetLineIndentation(SA::Line line, int indent) {
	if (indent < 0)
		return;
	const SA::Span rangeStart = GetSelection();
	SA::Span range = rangeStart;
	const SA::Position posBefore = GetLineIndentPosition(line);
	wEditor.SetLineIndentation(line, indent);
	wEditor2.SetLineIndentation(line, indent);
	const SA::Position posAfter = GetLineIndentPosition(line);
	const SA::Position posDifference = posAfter - posBefore;
	if (posAfter > posBefore) {
		// Move selection on
		if (range.start >= posBefore) {
			range.start += posDifference;
		}
		if (range.end >= posBefore) {
			range.end += posDifference;
		}
	} else if (posAfter < posBefore) {
		// Move selection back
		if (range.start >= posAfter) {
			if (range.start >= posBefore)
				range.start += posDifference;
			else
				range.start = posAfter;
		}
		if (range.end >= posAfter) {
			if (range.end >= posBefore)
				range.end += posDifference;
			else
				range.end = posAfter;
		}
	}
	if (!(rangeStart == range)) {
		SetSelection(range.start, range.end, *lEditor);
	}
}

int SciTEBase::GetLineIndentation(SA::Line line) {
	return lEditor->LineIndentation(line);
}

SA::Position SciTEBase::GetLineIndentPosition(SA::Line line) {
	return lEditor->LineIndentPosition(line);
}

namespace {

std::string CreateIndentation(int indent, int tabSize, bool insertSpaces) {
	std::string indentation;
	if (!insertSpaces) {
		while (indent >= tabSize) {
			indentation.append("\t", 1);
			indent -= tabSize;
		}
	}
	while (indent > 0) {
		indentation.append(" ", 1);
		indent--;
	}
	return indentation;
}

}

void SciTEBase::ConvertIndentation(int tabSize, int useTabs) {
	UndoBlock ub(*lEditor);
	const SA::Line maxLine = lEditor->LineCount();
	for (SA::Line line = 0; line < maxLine; line++) {
		const SA::Position lineStart = lEditor->LineStart(line);
		const int indent = GetLineIndentation(line);
		const SA::Position indentPos = GetLineIndentPosition(line);
		constexpr int maxIndentation = 1000;
		if (indent < maxIndentation) {
			std::string indentationNow = lEditor->StringOfRange(SA::Span(lineStart, indentPos));
			std::string indentationWanted = CreateIndentation(indent, tabSize, !useTabs);
			if (indentationNow != indentationWanted) {
				lEditor->SetTarget(SA::Span(lineStart, indentPos));
				lEditor->ReplaceTarget(indentationWanted);
			}
		}
	}
}

bool SciTEBase::RangeIsAllWhitespace(SA::Position start, SA::Position end) {
	TextReader acc(*lEditor);
	for (SA::Position i = start; i < end; i++) {
		if ((acc[i] != ' ') && (acc[i] != '\t'))
			return false;
	}
	return true;
}

std::vector<std::string> SciTEBase::GetLinePartsInStyle(SA::Line line, const StyleAndWords &saw) {
	std::vector<std::string> sv;
	TextReader acc(*lEditor);
	std::string s;
	const bool separateCharacters = saw.IsSingleChar();
	const SA::Position thisLineStart = lEditor->LineStart(line);
	const SA::Position nextLineStart = lEditor->LineStart(line + 1);
	for (SA::Position pos = thisLineStart; pos < nextLineStart; pos++) {
		if (acc.StyleAt(pos) == saw.Style()) {
			if (separateCharacters) {
				// Add one character at a time, even if there is an adjacent character in the same style
				if (s.length() > 0) {
					sv.push_back(s);
				}
				s = "";
			}
			s += acc[pos];
		} else if (s.length() > 0) {
			sv.push_back(s);
			s = "";
		}
	}
	if (s.length() > 0) {
		sv.push_back(s);
	}
	return sv;
}

IndentationStatus SciTEBase::GetIndentState(SA::Line line) {
	// C like language indentation defined by braces and keywords
	IndentationStatus indentState = IndentationStatus::none;
	const std::vector<std::string> controlIndents = GetLinePartsInStyle(line, statementIndent);
	for (const std::string &sIndent : controlIndents) {
		if (statementIndent.Includes(sIndent))
			indentState = IndentationStatus::keyWordStart;
	}
	const std::vector<std::string> controlEnds = GetLinePartsInStyle(line, statementEnd);
	for (const std::string &sEnd : controlEnds) {
		if (statementEnd.Includes(sEnd))
			indentState = IndentationStatus::none;
	}
	// Braces override keywords
	const std::vector<std::string> controlBlocks = GetLinePartsInStyle(line, blockEnd);
	for (const std::string &sBlock : controlBlocks) {
		if (blockEnd.Includes(sBlock))
			indentState = IndentationStatus::blockEnd;
		if (blockStart.Includes(sBlock))
			indentState = IndentationStatus::blockStart;
	}
	return indentState;
}

int SciTEBase::IndentOfBlock(SA::Line line) {
	if (line < 0)
		return 0;
	const int indentSize = lEditor->Indent();
	int indentBlock = GetLineIndentation(line);
	SA::Line backLine = line;
	IndentationStatus indentState = IndentationStatus::none;
	if (statementIndent.IsEmpty() && blockStart.IsEmpty() && blockEnd.IsEmpty())
		indentState = IndentationStatus::blockStart;	// Don't bother searching backwards

	SA::Line lineLimit = line - statementLookback;
	if (lineLimit < 0)
		lineLimit = 0;
	while ((backLine >= lineLimit) && (indentState == IndentationStatus::none)) {
		indentState = GetIndentState(backLine);
		if (indentState != IndentationStatus::none) {
			indentBlock = GetLineIndentation(backLine);
			if (indentState == IndentationStatus::blockStart) {
				if (!indentOpening)
					indentBlock += indentSize;
			}
			if (indentState == IndentationStatus::blockEnd) {
				if (indentClosing)
					indentBlock -= indentSize;
				if (indentBlock < 0)
					indentBlock = 0;
			}
			if ((indentState == IndentationStatus::keyWordStart) && (backLine == line))
				indentBlock += indentSize;
		}
		backLine--;
	}
	return indentBlock;
}

void SciTEBase::MaintainIndentation(char ch) {
	const SA::EndOfLine eolMode = lEditor->EOLMode();
	const SA::Line curLine = GetCurrentLineNumber();
	SA::Line lastLine = curLine - 1;

	if (((eolMode == SA::EndOfLine::CrLf || eolMode == SA::EndOfLine::Lf) && ch == '\n') ||
			(eolMode == SA::EndOfLine::Cr && ch == '\r')) {
		if (props.GetInt("indent.automatic")) {
			while (lastLine >= 0 && GetLineLength(lastLine) == 0)
				lastLine--;
		}
		int indentAmount = 0;
		if (lastLine >= 0) {
			indentAmount = GetLineIndentation(lastLine);
		}
		if (indentAmount > 0) {
			SetLineIndentation(curLine, indentAmount);
		}
	}
}

void SciTEBase::AutomaticIndentation(char ch) {
	const SA::Span range = lEditor->SelectionSpan();
	const SA::Position selStart = range.start;
	const SA::Line curLine = GetCurrentLineNumber();
	const SA::Position thisLineStart = lEditor->LineStart(curLine);
	const int indentSize = lEditor->Indent();
	int indentBlock = IndentOfBlock(curLine - 1);

	if ((lEditor->Lexer() == SCLEX_PYTHON) &&
			(props.GetInt("indent.python.colon") == 1)) {
		const SA::EndOfLine eolMode = lEditor->EOLMode();
		const int eolChar = (eolMode == SA::EndOfLine::Cr ? '\r' : '\n');
		const int eolChars = (eolMode == SA::EndOfLine::CrLf ? 2 : 1);
		const SA::Position prevLineStart = lEditor->LineStart(curLine - 1);
		const SA::Position prevIndentPos = GetLineIndentPosition(curLine - 1);
		const int indentExisting = GetLineIndentation(curLine);

		if (ch == eolChar) {
			// Find last noncomment, nonwhitespace character on previous line
			char character = '\0';
			int style = 0;
			for (SA::Position p = selStart - eolChars - 1; p > prevLineStart; p--) {
				style = lEditor->UnsignedStyleAt(p);
				if (style != SCE_P_DEFAULT && style != SCE_P_COMMENTLINE &&
						style != SCE_P_COMMENTBLOCK) {
					character = lEditor->CharacterAt(p);
					break;
				}
			}
			indentBlock = GetLineIndentation(curLine - 1);
			if (style == SCE_P_OPERATOR && character == ':') {
				SetLineIndentation(curLine, indentBlock + indentSize);
			} else if (selStart == prevIndentPos + eolChars) {
				// Preserve the indentation of preexisting text beyond the caret
				SetLineIndentation(curLine, indentBlock + indentExisting);
			} else {
				SetLineIndentation(curLine, indentBlock);
			}
		}
		return;
	}

	if (blockEnd.IsCharacter(ch)) {	// Dedent maybe
		if (!indentClosing) {
			if (RangeIsAllWhitespace(thisLineStart, selStart - 1)) {
				SetLineIndentation(curLine, indentBlock - indentSize);
			}
		}
	} else if (!blockEnd.IsSingleChar() && (ch == ' ')) {	// Dedent maybe
		if (!indentClosing && (GetIndentState(curLine) == IndentationStatus::blockEnd)) {}
	} else if (blockStart.IsCharacter(ch)) {
		// Dedent maybe if first on line and previous line was starting keyword
		if (!indentOpening && (GetIndentState(curLine - 1) == IndentationStatus::keyWordStart)) {
			if (RangeIsAllWhitespace(thisLineStart, selStart - 1)) {
				SetLineIndentation(curLine, indentBlock - indentSize);
			}
		}
	} else if ((ch == '\r' || ch == '\n') && (selStart == thisLineStart)) {
		if (!indentClosing && !blockEnd.IsSingleChar()) {	// Dedent previous line maybe
			const std::vector<std::string> controlWords = GetLinePartsInStyle(curLine - 1, blockEnd);
			if (!controlWords.empty()) {
				if (blockEnd.Includes(controlWords[0])) {
					// Check if first keyword on line is an ender
					SetLineIndentation(curLine - 1, IndentOfBlock(curLine - 2) - indentSize);
					// Recalculate as may have changed previous line
					indentBlock = IndentOfBlock(curLine - 1);
				}
			}
		}
		SetLineIndentation(curLine, indentBlock);
	}
}

/**
 * Upon a character being added, SciTE may decide to perform some action
 * such as displaying a completion list or auto-indentation.
 */
void SciTEBase::CharAdded(int utf32) {
	if (recording)
		return;
	const SA::Span rangeSelection = GetSelection();
	const SA::Position selStart = rangeSelection.start;
	const SA::Position selEnd = rangeSelection.end;

	if (utf32 > 0XFF) { // MBCS, never let it go.
		if (imeAutoComplete) {
			if ((selEnd == selStart) && (selStart > 0)) {
				if (lEditor->CallTipActive()) {
					ContinueCallTip();
				} else if (lEditor->AutoCActive()) {
					lEditor->AutoCCancel();
					StartAutoComplete();
				} else {
					StartAutoComplete();
				}
			}
		}
		return;
	}

	// SBCS
	const char ch = static_cast<char>(utf32);
	if ((selEnd == selStart) && (selStart > 0)) {
		if (lEditor->CallTipActive()) {
			if (Contains(calltipParametersEnd, ch)) {
				braceCount--;
				if (braceCount < 1)
					lEditor->CallTipCancel();
				else
					StartCallTip();
			} else if (Contains(calltipParametersStart, ch)) {
				braceCount++;
				StartCallTip();
			} else {
				ContinueCallTip();
			}
		} else if (lEditor->AutoCActive()) {
			if (Contains(calltipParametersStart, ch)) {
				braceCount++;
				StartCallTip();
			} else if (Contains(calltipParametersEnd, ch)) {
				braceCount--;
			} else if (!Contains(wordCharacters, ch)) {
				lEditor->AutoCCancel();
				if (Contains(autoCompleteStartCharacters, ch)) {
					StartAutoComplete();
				}
			} else if (autoCCausedByOnlyOne) {
				StartAutoCompleteWord(true);
			}
		} else if (HandleXml(ch)) {
			// Handled in the routine
		} else {
			if (Contains(calltipParametersStart, ch)) {
				braceCount = 1;
				StartCallTip();
			} else {
				autoCCausedByOnlyOne = false;
				if (indentMaintain)
					MaintainIndentation(ch);
				else if (props.GetInt("indent.automatic"))
					AutomaticIndentation(ch);
				if (Contains(autoCompleteStartCharacters, ch)) {
					StartAutoComplete();
				} else if (props.GetInt("autocompleteword.automatic") && Contains(wordCharacters, ch)) {
					StartAutoCompleteWord(true);
					autoCCausedByOnlyOne = lEditor->AutoCActive();
				}
			}
		}
	}
}

namespace {

void AddProps(AutoCompleteWordList &symbols, const PropSetFile &propSet) {
	const char *key = nullptr;
	const char *val = nullptr;
	for (bool b = propSet.GetFirst(key, val); b; b = propSet.GetNext(key, val)) {
		if (IsUpperCase(*key)) {
			symbols.Add(std::string(key) + ")");
		}
	}
}

constexpr int DigitsIn(SA::Line line) noexcept {
	constexpr SA::Line decimal = 10;
	int digits = 1;
	while (line >= decimal) {
		line /= decimal;
		++digits;
	}
	return digits;
}

}

/**
 * Upon a character being added to the output, SciTE may decide to perform some action
 * such as displaying a completion list or running a shell command.
 */
void SciTEBase::CharAddedOutput(int ch) {
	if (ch == '\n') {
		NewLineInOutput();
	} else if (ch == '(') {
		// Potential autocompletion of symbols when $( typed
		const SA::Position selStart = wOutput.SelectionStart();
		if ((selStart > 1) && (wOutput.CharacterAt(selStart - 2) == '$')) {
			AutoCompleteWordList symbols;
			AddProps(symbols, props);
			AddProps(symbols, propsDirectory);
			if (const std::string words = symbols.Sorted(true); !words.empty()) {
				wOutput.AutoCSetSeparator('\n');
				wOutput.AutoCSetMaxHeight(autoCompleteVisibleItemCount);
				wOutput.AutoCShow(0, words.c_str());
			}
		}
	}
}

/**
 * This routine will auto complete XML or HTML tags that are still open by closing them
 * @param ch The character we are dealing with, currently only works with the '>' character
 * @return True if handled, false otherwise
 */
bool SciTEBase::HandleXml(char ch) {
	// We're looking for this char
	// Quit quickly if not found
	if (ch != '>') {
		return false;
	}

	// This may make sense only in certain languages
	if (lexLanguage != SCLEX_HTML && lexLanguage != SCLEX_XML) {
		return false;
	}

	// If the user has turned us off, quit now.
	// Default is off
	const std::string value = props.GetExpandedString("xml.auto.close.tags");
	if ((value.length() == 0) || (value == "0")) {
		return false;
	}

	// Grab the last 512 characters or so
	const SA::Position nCaret = lEditor->CurrentPos();
	SA::Position nMin = nCaret - 512;
	if (nMin < 0) {
		nMin = 0;
	}

	if (nCaret - nMin < 3) {
		return false; // Smallest tag is 3 characters ex. <p>
	}
	std::string sel = lEditor->StringOfRange(SA::Span(nMin, nCaret));

	if (sel[nCaret - nMin - 2] == '/') {
		// User typed something like "<br/>"
		return false;
	}

	if (sel[nCaret - nMin - 2] == '-') {
		// User typed something like "<a $this->"
		return false;
	}

	std::string strFound = FindOpenXmlTag(sel.c_str(), nCaret - nMin);

	if (strFound.length() > 0) {
		UndoBlock ub(*lEditor);
		std::string toInsert = "</";
		toInsert += strFound;
		toInsert += ">";
		lEditor->ReplaceSel(toInsert.c_str());
		SetSelection(nCaret, nCaret, *lEditor);
		return true;
	}

	return false;
}

/** Search backward through nSize bytes looking for a '<', then return the tag if any
 * @return The tag name
 */
std::string SciTEBase::FindOpenXmlTag(const char sel[], SA::Position nSize) {
	std::string strRet;

	if (nSize < 3) {
		// Smallest tag is "<p>" which is 3 characters
		return strRet;
	}
	const char *pBegin = &sel[0];
	const char *pCur = &sel[nSize - 1];

	pCur--; // Skip past the >
	while (pCur > pBegin) {
		if (*pCur == '<') {
			break;
		} else if (*pCur == '>') {
			if (*(pCur - 1) != '-') {
				break;
			}
		}
		--pCur;
	}

	if (*pCur == '<') {
		pCur++;
		while (strchr(":_-.", *pCur) || IsAlphaNumeric(*pCur)) {
			strRet += *pCur;
			pCur++;
		}
	}

	// Return the tag name or ""
	return strRet;
}

void SciTEBase::GoMatchingBrace(bool select) {
	SA::Position braceAtCaret = -1;
	SA::Position braceOpposite = -1;
	const bool isInside = FindMatchingBracePosition(pwFocussed == lEditor, braceAtCaret, braceOpposite, true);
	// Convert the character positions into caret positions based on whether
	// the caret position was inside or outside the braces.
	if (isInside) {
		if (braceOpposite > braceAtCaret) {
			braceAtCaret++;
		} else if (braceOpposite >= 0) {
			braceOpposite++;
		}
	} else {    // Outside
		if (braceOpposite > braceAtCaret) {
			braceOpposite++;
		} else {
			braceAtCaret++;
		}
	}
	if (braceOpposite >= 0) {
		EnsureRangeVisible(*pwFocussed, SA::Span(braceOpposite));
		if (select) {
			pwFocussed->SetSel(braceAtCaret, braceOpposite);
		} else {
			pwFocussed->SetSel(braceOpposite, braceOpposite);
		}
	}
}

// Text	ConditionalUp	Ctrl+J	Finds the previous matching preprocessor condition
// Text	ConditionalDown	Ctrl+K	Finds the next matching preprocessor condition
void SciTEBase::GoMatchingPreprocCond(int direction, bool select) {
	const SA::Position mppcAtCaret = lEditor->CurrentPos();
	SA::Position mppcMatch = -1;
	const int forward = (direction == IDM_NEXTMATCHPPC);
	const bool isInside = FindMatchingPreprocCondPosition(forward, mppcAtCaret, mppcMatch);

	if (isInside && mppcMatch >= 0) {
		EnsureRangeVisible(*lEditor, SA::Span(mppcMatch));
		if (select) {
			// Selection changes the rules a bit...
			const SA::Position selStart = lEditor->SelectionStart();
			const SA::Position selEnd = lEditor->SelectionEnd();
			// pivot isn't the caret position but the opposite (if there is a selection)
			const SA::Position pivot = (mppcAtCaret == selStart ? selEnd : selStart);
			if (forward) {
				// Caret goes one line beyond the target, to allow selecting the whole line
				const SA::Line lineNb = lEditor->LineFromPosition(mppcMatch);
				mppcMatch = lEditor->LineStart(lineNb + 1);
			}
			SetSelection(pivot, mppcMatch, *lEditor);
		} else {
			SetSelection(mppcMatch, mppcMatch, *lEditor);
		}
	} else {
		WarnUser(warnNotFound);
	}
}

void SciTEBase::AddCommand(std::string_view cmd, std::string_view dir, JobSubsystem jobType, std::string_view input, int flags) {
	// If no explicit directory, use the directory of the current file
	FilePath directoryRun;
	if (dir.length()) {
		FilePath directoryExplicit(GUI::StringFromUTF8(dir));
		if (directoryExplicit.IsAbsolute()) {
			directoryRun = directoryExplicit;
		} else {
			// Relative paths are relative to the current file
			directoryRun = FilePath(filePath.Directory(), directoryExplicit).NormalizePath();
		}
	} else {
		directoryRun = filePath.Directory();
	}
	jobQueue.AddCommand(cmd, directoryRun, jobType, input, flags);
}

int ControlIDOfCommand(unsigned long wParam) noexcept {
	return wParam & 0xffff;
}

void WindowSetFocus(GUI::ScintillaWindow &w) {
	w.Send(SCI_GRABFOCUS);
}

void SciTEBase::SetFoldWidth() {
	wEditor.SetMarginWidthN(2, (foldMargin && !FilterShowing()) ? foldMarginWidth : 0);
	wEditor2.SetMarginWidthN(2, (foldMargin && !FilterShowing()) ? foldMarginWidth : 0);
}

void SciTEBase::SetLineNumberWidth() {
	if (lineNumbers) {
		int lineNumWidth = lineNumbersWidth;
		if (lineNumbersExpand) {
			// The margin size will be expanded if the current buffer's maximum
			// line number would overflow the margin.
			lineNumWidth = std::max(DigitsIn(wEditor.LineCount()), lineNumbersWidth);
		}
		lineNumWidth = std::max(0, lineNumWidth);	// No negative width
		// The 4 here allows for spacing: 1 pixel on left and 3 on right.
		std::string nNines(lineNumWidth, '9');
		const int pixelWidth = 4 + wEditor.TextWidth(
					       static_cast<int>(SA::StylesCommon::LineNumber), nNines.c_str());

		wEditor.SetMarginWidthN(0, pixelWidth);
		wEditor2.SetMarginWidthN(0, pixelWidth);
	} else {
		wEditor.SetMarginWidthN(0, 0);
		wEditor2.SetMarginWidthN(0, 0);
	}
}

void SciTEBase::MenuCommand(int cmdID, int source) {
	switch (cmdID) {
	case IDM_NEW:
		// For the New command, the "are you sure" question is always asked as this gives
		// an opportunity to abandon the edits made to a file when are.you.sure is turned off.
		if (CanMakeRoom()) {
			New();
			ReadProperties();
			SetIndentSettings();
			SetEol();
			UpdateStatusBar(true);
			WindowSetFocus(*lEditor);
		}
		break;
	case IDM_OPEN:
		// No need to see if can make room as that will occur
		// when doing the opening. Must be done there as user
		// may decide to open multiple files so do not know yet
		// how much room needed.
		OpenDialog(filePath.Directory(), GUI::StringFromUTF8(props.GetExpandedString("open.filter")));
		WindowSetFocus(*lEditor);
		break;
	case IDM_OPENSELECTED:
		if (OpenSelected())
			WindowSetFocus(*lEditor);
		break;
	case IDM_REVERT:
		Revert();
		WindowSetFocus(*lEditor);
		break;
	case IDM_CLOSE:
		if (SaveIfUnsure() != SaveResult::cancelled) {
			Close();
			WindowSetFocus(*lEditor);
		}
		break;
	case IDM_CLOSEALL:
		CloseAllBuffers();
		break;
	case IDM_CLOSEALL_BUT_CURRENT:
		CloseAllBuffersButCurrent();
		break;
	case IDM_SAVE:
		Save();
		WindowSetFocus(*lEditor);
		break;
	case IDM_SAVEALL:
		SaveAllBuffers(true);
		break;
	case IDM_RENAME:
		ShowRenameDialog();
		break;
	case IDM_SAVEAS:
		SaveAsDialog();
		WindowSetFocus(*lEditor);
		break;
	case IDM_SAVEACOPY:
		SaveACopy();
		WindowSetFocus(*lEditor);
		break;
	case IDM_COPYPATH:
		CopyPath();
		break;
	case IDM_SAVEASHTML:
		SaveAsHTML();
		WindowSetFocus(*lEditor);
		break;
	case IDM_SAVEASRTF:
		SaveAsRTF();
		WindowSetFocus(*lEditor);
		break;
	case IDM_SAVEASPDF:
		SaveAsPDF();
		WindowSetFocus(*lEditor);
		break;
	case IDM_SAVEASTEX:
		SaveAsTEX();
		WindowSetFocus(*lEditor);
		break;
	case IDM_SAVEASXML:
		SaveAsXML();
		WindowSetFocus(*lEditor);
		break;
	case IDM_PRINT:
		Print(true);
		break;
	case IDM_PRINTSETUP:
		PrintSetup();
		break;
	case IDM_LOADSESSION:
		LoadSessionDialog();
		WindowSetFocus(*lEditor);
		break;
	case IDM_SAVESESSION:
		SaveSessionDialog();
		WindowSetFocus(*lEditor);
		break;
	case IDM_ABOUT:
		AboutDialog();
		break;
	case IDM_QUIT:
		QuitProgram();
		break;
	case IDM_ENCODING_DEFAULT:
	case IDM_ENCODING_UCS2BE:
	case IDM_ENCODING_UCS2LE:
	case IDM_ENCODING_UTF8:
	case IDM_ENCODING_UCOOKIE:
		CurrentBuffer()->unicodeMode = static_cast<UniMode>(cmdID - IDM_ENCODING_DEFAULT);
		if (CurrentBuffer()->unicodeMode != UniMode::uni8Bit) {
			// Override the code page if Unicode
			codePage = SA::CpUtf8;
		} else {
			codePage = props.GetInt("code.page");
		}
		wEditor.SetCodePage(codePage);
		wEditor2.SetCodePage(codePage);
		UpdateStatusBar(false);
		break;

	case IDM_C_ENCODING_DEFAULT:
	case IDM_C_ENCODING_UCS2BE:
	case IDM_C_ENCODING_UCS2LE:
	case IDM_C_ENCODING_UTF8:
	case IDM_C_ENCODING_UCOOKIE:
		ChangeBufferEncoding(static_cast<UniMode>(cmdID - IDM_C_ENCODING_DEFAULT));
		UpdateStatusBar(false);
		break;

	case IDM_NEXTFILESTACK:
		if (buffers.size() > 1 && props.GetInt("buffers.zorder.switching")) {
			NextInStack(); // next most recently selected buffer
			WindowSetFocus(*lEditor);
			break;
		}
		[[fallthrough]];
	// else fall through and do NEXTFILE behaviour...
	case IDM_NEXTFILE:
		if (buffers.size() > 1) {
			Next(); // Use Next to tabs move left-to-right
			WindowSetFocus(*lEditor);
		} else {
			// Not using buffers - switch to next file on MRU
			StackMenuNext();
		}
		break;

	case IDM_PREVFILESTACK:
		if (buffers.size() > 1 && props.GetInt("buffers.zorder.switching")) {
			PrevInStack(); // next least recently selected buffer
			WindowSetFocus(*lEditor);
			break;
		}
		[[fallthrough]];
	// else fall through and do PREVFILE behaviour...
	case IDM_PREVFILE:
		if (buffers.size() > 1) {
			Prev(); // Use Prev to tabs move right-to-left
			WindowSetFocus(*lEditor);
		} else {
			// Not using buffers - switch to previous file on MRU
			StackMenuPrev();
		}
		break;

	case IDM_MOVETABRIGHT:
		MoveTabRight();
		WindowSetFocus(*lEditor);
		break;
	case IDM_MOVETABLEFT:
		MoveTabLeft();
		WindowSetFocus(*lEditor);
		break;

	case IDM_UNDO:
		PaneSource(source).Undo();
		CheckMenus();
		break;
	case IDM_REDO:
		PaneSource(source).Redo();
		CheckMenus();
		break;

	case IDM_CUT:
		if (!PaneSource(source).SelectionEmpty()) {
			PaneSource(source).Cut();
		}
		break;
	case IDM_COPY:
		if (!PaneSource(source).SelectionEmpty()) {
			//fprintf(stderr, "Copy from %d\n", source);
			PaneSource(source).Copy();
		}
		// does not trigger Notification::UpdateUI, so do CheckMenusClipboard() here
		CheckMenusClipboard();
		break;
	case IDM_PASTE:
		PaneSource(source).Paste();
		break;
	case IDM_DUPLICATE:
		PaneSource(source).SelectionDuplicate();
		break;
	case IDM_PASTEANDDOWN: {
			const SA::Position pos = PaneFocused().CurrentPos();
			PaneFocused().Paste();
			PaneFocused().SetCurrentPos(pos);
			PaneFocused().CharLeft();
			PaneFocused().LineDown();
		}
		break;
	case IDM_DROPSELECTION:
		DropSelectionAt(PaneFocused(), contextSelection);
		break;
	case IDM_CLEAR:
		PaneSource(source).Clear();
		break;
	case IDM_SELECTALL:
		PaneSource(source).SelectAll();
		break;
	case IDM_COPYASRTF:
		CopyAsRTF();
		break;

	case IDM_FIND:
		Find();
		break;

	case IDM_INCSEARCH:
		IncrementSearchMode();
		break;

	case IDM_FILTER:
		FilterSearch();
		break;

	case IDM_FINDNEXT:
		FindNext(reverseFind);
		break;

	case IDM_FINDNEXTBACK:
		FindNext(!reverseFind);
		break;

	case IDM_FINDNEXTSEL:
		SelectionIntoFind();
		FindNext(reverseFind, true, false);
		break;

	case IDM_ENTERSELECTION:
		SelectionIntoFind();
		break;

	case IDM_SELECTIONADDNEXT:
		SelectionAdd(AddSelection::next);
		break;

	case IDM_SELECTIONADDEACH:
		SelectionAdd(AddSelection::each);
		break;

	case IDM_FINDNEXTBACKSEL:
		SelectionIntoFind();
		FindNext(!reverseFind, true, false);
		break;

	case IDM_FINDINFILES:
		FindInFiles();
		break;

	case IDM_REPLACE:
		Replace();
		break;

	case IDM_GOTO:
		GoLineDialog();
		break;

	case IDM_MATCHBRACE:
		GoMatchingBrace(false);
		break;

	case IDM_SELECTTOBRACE:
		GoMatchingBrace(true);
		break;

	case IDM_PREVMATCHPPC:
		GoMatchingPreprocCond(IDM_PREVMATCHPPC, false);
		break;

	case IDM_SELECTTOPREVMATCHPPC:
		GoMatchingPreprocCond(IDM_PREVMATCHPPC, true);
		break;

	case IDM_NEXTMATCHPPC:
		GoMatchingPreprocCond(IDM_NEXTMATCHPPC, false);
		break;

	case IDM_SELECTTONEXTMATCHPPC:
		GoMatchingPreprocCond(IDM_NEXTMATCHPPC, true);
		break;
	case IDM_SHOWCALLTIP:
		if (lEditor->CallTipActive()) {
			currentCallTip = (currentCallTip + 1 == maxCallTips) ? 0 : currentCallTip + 1;
			FillFunctionDefinition();
		} else {
			StartCallTip();
		}
		break;
	case IDM_COMPLETE:
		autoCCausedByOnlyOne = false;
		StartAutoComplete();
		break;

	case IDM_COMPLETEWORD:
		autoCCausedByOnlyOne = false;
		StartAutoCompleteWord(false);
		break;

	case IDM_ABBREV:
		lEditor->Cancel();
		StartExpandAbbreviation();
		break;

	case IDM_INS_ABBREV:
		lEditor->Cancel();
		AbbrevDialog();
		break;

	case IDM_BLOCK_COMMENT:
		StartBlockComment();
		break;

	case IDM_BOX_COMMENT:
		StartBoxComment();
		break;

	case IDM_STREAM_COMMENT:
		StartStreamComment();
		break;

	case IDM_TOGGLE_FOLDALL:
		FoldAll();
		break;

	case IDM_UPRCASE:
		PaneFocused().UpperCase();
		break;

	case IDM_LWRCASE:
		PaneFocused().LowerCase();
		break;

	case IDM_LINEREVERSE:
		PaneFocused().LineReverse();
		break;

	case IDM_JOIN:
		PaneFocused().TargetFromSelection();
		PaneFocused().LinesJoin();
		break;

	case IDM_SPLIT:
		PaneFocused().TargetFromSelection();
		PaneFocused().LinesSplit(0);
		break;

	case IDM_EXPAND:
		lEditor->ToggleFold(GetCurrentLineNumber());
		break;

	case IDM_TOGGLE_FOLDRECURSIVE: {
			const SA::Line line = GetCurrentLineNumber();
			const SA::FoldLevel level = lEditor->FoldLevel(line);
			ToggleFoldRecursive(line, level, *lEditor);
		}
		break;

	case IDM_EXPAND_ENSURECHILDRENVISIBLE: {
			const SA::Line line = GetCurrentLineNumber();
			const SA::FoldLevel level = lEditor->FoldLevel(line);
			EnsureAllChildrenVisible(line, level);
		}
		break;

	case IDM_SPLITVERTICAL: {
			const GUI::Rectangle rcClient = GetClientRectangle();
			const double doubleHeightOutput = heightOutput;
			const double doublePreviousHeightOutput = previousHeightOutput;
			heightOutput = static_cast<int>(splitVertical ?
							std::lround(doubleHeightOutput * rcClient.Height() / rcClient.Width()) :
							std::lround(doubleHeightOutput * rcClient.Width() / rcClient.Height()));
			previousHeightOutput = static_cast<int>(splitVertical ?
								std::lround(doublePreviousHeightOutput * rcClient.Height() / rcClient.Width()) :
								std::lround(doublePreviousHeightOutput * rcClient.Width() / rcClient.Height()));
		}
		splitVertical = !splitVertical;
		heightOutput = NormaliseSplit(heightOutput);
		heightEditorSplit = NormaliseESplit(heightEditorSplit);
		previousHeightwEditor2 = heightEditorSplit;
		SizeSubWindows();
		CheckMenus();
		Redraw();
		break;

	case IDM_LINENUMBERMARGIN:
		lineNumbers = !lineNumbers;
		SetLineNumberWidth();
		CheckMenus();
		break;

	case IDM_SELMARGIN:
		margin = !margin;
		wEditor.SetMarginWidthN(1, margin ? marginWidth : 0);
		wEditor2.SetMarginWidthN(1, margin ? marginWidth : 0);
		CheckMenus();
		break;

	case IDM_FOLDMARGIN:
		foldMargin = !foldMargin;
		SetFoldWidth();
		CheckMenus();
		break;

	case IDM_VIEWEOL:
		wEditor.SetViewEOL(!wEditor.ViewEOL());
		wEditor2.SetViewEOL(wEditor.ViewEOL());
		CheckMenus();
		break;

	case IDM_VIEWTOOLBAR:
		tbVisible = !tbVisible;
		ShowToolBar();
		CheckMenus();
		break;

	case IDM_TOGGLEOUTPUT:
		ToggleOutputVisible();
		CheckMenus();
		break;

	case IDM_TOGGLEPARAMETERS:
		ParametersDialog(false);
		CheckMenus();
		break;

	case IDM_WRAP:
		wrap = !wrap;
		wEditor.SetWrapMode(wrap ? wrapStyle : SA::Wrap::None);
		wEditor2.SetWrapMode(wrap ? wrapStyle : SA::Wrap::None);
		CheckMenus();
		break;

	case IDM_WRAPOUTPUT:
		wrapOutput = !wrapOutput;
		wOutput.SetWrapMode(wrapOutput ? wrapStyle : SA::Wrap::None);
		CheckMenus();
		break;

	case IDM_SPLITSCREEN:
		ToggleEditor2Visible();
		break;

	case IDM_READONLY:
		CurrentBuffer()->isReadOnly = !CurrentBuffer()->isReadOnly;
		wEditor.SetReadOnly(CurrentBuffer()->isReadOnly);
		wEditor2.SetReadOnly(CurrentBuffer()->isReadOnly);
		UpdateStatusBar(true);
		CheckMenus();
		SetBuffersMenu();
		SetWindowName();
		break;

	case IDM_VIEWTABBAR:
		tabVisible = !tabVisible;
		ShowTabBar();
		CheckMenus();
		break;

	case IDM_VIEWSTATUSBAR:
		sbVisible = !sbVisible;
		ShowStatusBar();
		UpdateStatusBar(true);
		CheckMenus();
		break;

	case IDM_CLEAROUTPUT:
		wOutput.ClearAll();
		break;

	case IDM_SWITCHPANE:
		if (pwFocussed == lEditor)
			WindowSetFocus(wOutput);
		else
			WindowSetFocus(*lEditor);
		break;

	case IDM_EOL_CRLF:
		wEditor.SetEOLMode(SA::EndOfLine::CrLf);
		wEditor2.SetEOLMode(SA::EndOfLine::CrLf);
		CheckMenus();
		UpdateStatusBar(false);
		break;

	case IDM_EOL_CR:
		wEditor.SetEOLMode(SA::EndOfLine::Cr);
		wEditor2.SetEOLMode(SA::EndOfLine::Cr);
		CheckMenus();
		UpdateStatusBar(false);
		break;
	case IDM_EOL_LF:
		wEditor.SetEOLMode(SA::EndOfLine::Lf);
		wEditor2.SetEOLMode(SA::EndOfLine::Lf);
		CheckMenus();
		UpdateStatusBar(false);
		break;
	case IDM_EOL_CONVERT:
		lEditor->ConvertEOLs(lEditor->EOLMode());
		break;

	case IDM_VIEWSPACE:
		ViewWhitespace(wEditor.ViewWS() == SA::WhiteSpace::Invisible);
		CheckMenus();
		Redraw();
		break;

	case IDM_VIEWGUIDES: {
			const bool viewIG = wEditor.IndentationGuides() == SA::IndentView::None;
			wEditor.SetIndentationGuides(viewIG ? indentExamine : SA::IndentView::None);
			wEditor2.SetIndentationGuides(viewIG ? indentExamine : SA::IndentView::None);
			CheckMenus();
			Redraw();
		}
		break;

	case IDM_COMPILE: {
			if (SaveIfUnsureForBuilt() != SaveResult::cancelled) {
				SelectionIntoProperties();
				AddCommand(props.GetWild("command.compile.", FileNameExt().AsUTF8()), "",
					   SubsystemType("command.compile.subsystem."));
				if (jobQueue.HasCommandToRun())
					Execute();
			}
		}
		break;

	case IDM_BUILD: {
			if (SaveIfUnsureForBuilt() != SaveResult::cancelled) {
				SelectionIntoProperties();
				AddCommand(
					props.GetWild("command.build.", FileNameExt().AsUTF8()),
					props.GetNewExpandString("command.build.directory.", FileNameExt().AsUTF8()),
					SubsystemType("command.build.subsystem."));
				if (jobQueue.HasCommandToRun()) {
					jobQueue.isBuilding = true;
					Execute();
				}
			}
		}
		break;

	case IDM_CLEAN: {
			if (SaveIfUnsureForBuilt() != SaveResult::cancelled) {
				SelectionIntoProperties();
				AddCommand(props.GetWild("command.clean.", FileNameExt().AsUTF8()), "",
					   SubsystemType("command.clean.subsystem."));
				if (jobQueue.HasCommandToRun())
					Execute();
			}
		}
		break;

	case IDM_GO_ALT:
	case IDM_GO: {
			if (SaveIfUnsureForBuilt() != SaveResult::cancelled) {
				SelectionIntoProperties();
				int flags = 0;

				if (!jobQueue.isBuilt) {
					std::string buildcmd = props.GetNewExpandString("command.go.needs.", FileNameExt().AsUTF8());
					AddCommand(buildcmd, "",
						   SubsystemType("command.go.needs.subsystem."));
					if (buildcmd.length() > 0) {
						jobQueue.isBuilding = true;
						flags |= jobForceQueue;
					}
				}
				AddCommand(props.GetWild("command.go.", FileNameExt().AsUTF8()), "",
					   SubsystemType("command.go.subsystem."), "", flags);
				if (jobQueue.HasCommandToRun())
					Execute();
			}
		}
		break;

	case IDM_COM_LIST:
		FindFunctions();
		break;

	case IDM_STOPEXECUTE:
		StopExecute();
		break;

	case IDM_NEXTMSG:
		GoMessage(1);
		break;

	case IDM_PREVMSG:
		GoMessage(-1);
		break;

	case IDM_OPENLOCALPROPERTIES:
		OpenProperties(IDM_OPENLOCALPROPERTIES);
		WindowSetFocus(*lEditor);
		break;

	case IDM_OPENUSERPROPERTIES:
		OpenProperties(IDM_OPENUSERPROPERTIES);
		WindowSetFocus(*lEditor);
		break;

	case IDM_OPENGLOBALPROPERTIES:
		OpenProperties(IDM_OPENGLOBALPROPERTIES);
		WindowSetFocus(*lEditor);
		break;

	case IDM_OPENABBREVPROPERTIES:
		OpenProperties(IDM_OPENABBREVPROPERTIES);
		WindowSetFocus(*lEditor);
		break;

	case IDM_OPENLUAEXTERNALFILE:
		OpenProperties(IDM_OPENLUAEXTERNALFILE);
		WindowSetFocus(*lEditor);
		break;

	case IDM_OPENDIRECTORYPROPERTIES:
		OpenProperties(IDM_OPENDIRECTORYPROPERTIES);
		WindowSetFocus(*lEditor);
		break;

	case IDM_SRCWIN:
	case IDM_SRCWIN2:
		break;

	case IDM_BOOKMARK_TOGGLE:
		BookmarkToggle(markerUserBookmark);
		SyncMarkersToMap();
		break;

	case IDM_BOOKMARK_NEXT:
		BookmarkNext(true);
		break;

	case IDM_BOOKMARK_PREV:
		BookmarkNext(false);
		break;

	case IDM_BOOKMARK_NEXT_SELECT:
		BookmarkNext(true, true);
		break;

	case IDM_BOOKMARK_PREV_SELECT:
		BookmarkNext(false, true);
		break;

	case IDM_BOOKMARK_CLEARALL:
		wEditor.MarkerDeleteAll(markerBookmark);
		RemoveFindMarks();
		wMarkerMap.MarkerDeleteAll(MarkBookMarks);
		break;

	case IDM_USERBOOKMARK_CLEARALL:
		wEditor.MarkerDeleteAll(markerUserBookmark);
		wMarkerMap.MarkerDeleteAll(MarkUserBookMarks);
		break;

	case IDM_BOOKMARK_SELECT_ALL:
		BookmarkSelectAll();
		break;

	case IDM_TABSIZE:
		TabSizeDialog();
		break;

	case IDM_MONOFONT:
		CurrentBuffer()->useMonoFont = !CurrentBuffer()->useMonoFont;
		ReadFontProperties();
		Redraw();
		break;

	case IDM_MACROLIST:
		AskMacroList();
		break;
	case IDM_MACROPLAY:
		StartPlayMacro();
		break;
	case IDM_MACRORECORD:
		StartRecordMacro();
		break;
	case IDM_MACROSTOPRECORD:
		StopRecordMacro();
		break;

	case IDM_HELP: {
			SelectionIntoProperties();
			AddCommand(props.GetWild("command.help.", FileNameExt().AsUTF8()), "",
				   SubsystemType("command.help.subsystem."));
			if (!jobQueue.IsExecuting() && jobQueue.HasCommandToRun()) {
				jobQueue.isBuilding = true;
				Execute();
			}
		}
		break;

	case IDM_HELP_SCITE: {
			SelectionIntoProperties();
			AddCommand(props.Get("command.scite.help"), "",
				   SubsystemFromChar(props.GetString("command.scite.help.subsystem")[0]));
			if (!jobQueue.IsExecuting() && jobQueue.HasCommandToRun()) {
				jobQueue.isBuilding = true;
				Execute();
			}
		}
		break;

	default:
		if ((cmdID >= bufferCmdID) &&
				(cmdID < bufferCmdID + buffers.size())) {
			SetDocumentAt(cmdID - bufferCmdID);
			CheckReload();
		} else if ((cmdID >= fileStackCmdID) &&
				(cmdID < fileStackCmdID + fileStackMax)) {
			StackMenu(cmdID - fileStackCmdID);
		} else if (cmdID >= importCmdID &&
				(cmdID < importCmdID + importMax)) {
			ImportMenu(cmdID - importCmdID);
		} else if (cmdID >= IDM_TOOLS && cmdID < IDM_TOOLS + toolMax) {
			ToolsMenu(cmdID - IDM_TOOLS);
		} else if (cmdID >= IDM_LANGUAGE && cmdID < IDM_LANGUAGE + 100) {
			SetOverrideLanguage(cmdID - IDM_LANGUAGE);
		} else if (cmdID >= SCI_START) {
			PaneFocused().Call(static_cast<SA::Message>(cmdID));
		}
		break;
	}
}



namespace {

int CodePageFromName(const std::string& encodingName) noexcept {
	struct Encoding {
		const char* name;
		int codePage;
	};
	const auto knownEncodings = std::to_array<Encoding>({
		{ "ascii", CP_UTF8 },
		{ "utf-8", CP_UTF8 },
		{ "latin1", 1252 },
		{ "latin2", 28592 },
		{ "big5", 950 },
		{ "gbk", 936 },
		{ "shift_jis", 932 },
		{ "euc-kr", 949 },
		{ "cyrillic", 1251 },
		{ "iso-8859-5", 28595 },
		{ "iso8859-11", 874 },
		{ "1250", 1250 },
		{ "windows-1251", 1251 },
		});
	for (const Encoding& enc : knownEncodings) {
		if (encodingName == enc.name) {
			return enc.codePage;
		}
	}
	return CP_UTF8;
}

std::string StringEncode(std::wstring_view wsv, int codePage) {
	if (wsv.empty()) {
		return {};
	}
	const int sLength = static_cast<int>(wsv.length());
	const int cchMulti = ::WideCharToMultiByte(codePage, 0, wsv.data(), sLength, nullptr, 0, nullptr, nullptr);
	std::string sMulti(cchMulti, 0);
	::WideCharToMultiByte(codePage, 0, wsv.data(), sLength, sMulti.data(), cchMulti, nullptr, nullptr);
	return sMulti;
}

std::wstring StringDecode(std::string_view sv, int codePage) {
	if (sv.empty()) {
		return {};
	}
	const int sLength = static_cast<int>(sv.length());
	const int cchWide = ::MultiByteToWideChar(codePage, 0, sv.data(), sLength, nullptr, 0);
	std::wstring sWide(cchWide, 0);
	::MultiByteToWideChar(codePage, 0, sv.data(), sLength, sWide.data(), cchWide);
	return sWide;
}

// Convert to UTF-8
std::string ConvertEncoding(std::string_view original, int codePage) {
	if (codePage == CP_UTF8) {
		return std::string(original);
	}
	GUI::gui_string sWide = StringDecode(original, codePage);
	return GUI::UTF8FromString(sWide);
}

int GetCodePageFromMode(UniMode mode) noexcept {
	switch (mode) {
	case UniMode::utf8:       // UTF-8 с BOM (или просто UTF-8 в ряде версий)
	case UniMode::cookie:    // UTF-8 без BOM
	case UniMode::uni16BE:    // UTF-16 Big Endian
	case UniMode::uni16LE:    // UTF-16 Little Endian
		return 65001;         // CP_UTF8
	case UniMode::uni8Bit:     // Системная кодировка (ANSI)
	default:
		return 0;
	}
}

}

void SciTEBase::ChangeBufferEncoding(UniMode newMode) {

	//if (CurrentBuffer()->file.IsSet() && !CurrentBuffer()->file.IsUntitled()) {
	//	Revert();
	//}

	Sci_Position len = wEditor.Length();
	if (len <= 0) return;

	SA::Line savePos = wEditor.FirstVisibleLine();
	SA::Line savePos2 = wEditor2.FirstVisibleLine();

	std::string rawBytes(len, '\0');
	Sci_TextRange tr = { {0, len}, &rawBytes.front() };
	wEditor.GetTextRange(reinterpret_cast<void*>(&tr));

	int hadBOM = 0;
	if (rawBytes.length() >= 3) {
		if (static_cast<unsigned char>(rawBytes[0]) == 0xEF &&
			static_cast<unsigned char>(rawBytes[1]) == 0xBB &&
			static_cast<unsigned char>(rawBytes[2]) == 0xBF) {
				hadBOM = 3;
		}
		if ((static_cast<unsigned char>(rawBytes[0]) == 0xFE && static_cast<unsigned char>(rawBytes[1]) == 0xFF) || 
			(static_cast<unsigned char>(rawBytes[0]) == 0xFF && static_cast<unsigned char>(rawBytes[1]) == 0xFE)) {
				hadBOM = 2;
		}
	}
	if (hadBOM) {
		rawBytes.erase(0, hadBOM);
	}

	int sourceCP = GetCodePageFromMode(CurrentBuffer()->unicodeMode);
	if (sourceCP == 0) sourceCP = props.GetInt("code.page");
	std::string utf8Text = ConvertEncoding(rawBytes, sourceCP);

	std::string finalData;
	if (newMode == UniMode::utf8) {
		finalData = "\xEF\xBB\xBF";
		finalData += utf8Text;
	}
	else if (newMode == UniMode::uni16BE) {
		finalData = "\xFE\xFF";
		finalData += utf8Text;
	}
	else if (newMode == UniMode::uni16LE) {
		finalData = "\xFF\xFE";
		finalData += utf8Text;
	}
	else {
		finalData = std::move(utf8Text);
	}

	wEditor.SetRedraw(false);
	wEditor2.SetRedraw(false);

	CurrentBuffer()->unicodeMode = newMode;

	int scCP = GetCodePageFromMode(newMode);
	if (scCP == 0) scCP = props.GetInt("code.page");
	wEditor.SetCodePage(scCP);
	wEditor2.SetCodePage(scCP);

	UndoBlock ub(wEditor);

	wEditor.ClearAll();
	wEditor.AddText(finalData.length(), finalData.c_str());
	
	wEditor.SetFirstVisibleLine(savePos);
	wEditor2.SetFirstVisibleLine(savePos2);

	wEditor.SetRedraw(true);
	wEditor2.SetRedraw(true);
	Redraw();
}

void SciTEBase::FoldChanged(SA::Line line, SA::FoldLevel levelNow, SA::FoldLevel levelPrev, GUI::ScintillaWindow& wEditor) {
	// Unfold any regions where the new fold structure makes that fold wrong.
	// Will only unfold and show lines and never fold or hide lines.
	if (LevelIsHeader(levelNow)) {
		if (!(LevelIsHeader(levelPrev))) {
			// Adding a fold point.
			wEditor.SetFoldExpanded(line, true);
			if (!wEditor.AllLinesVisible())
				ExpandFolds(line, true, levelPrev, wEditor);
		}
	} else if (LevelIsHeader(levelPrev)) {
		const SA::Line prevLine = line - 1;
		const SA::FoldLevel levelPrevLine = wEditor.FoldLevel(prevLine);

		// Combining two blocks where the first block is collapsed (e.g. by deleting the line(s) which separate(s) the two blocks)
		if ((LevelNumberPart(levelPrevLine) == LevelNumberPart(levelNow)) && !wEditor.LineVisible(prevLine)) {
			const SA::Line parentLine = wEditor.FoldParent(prevLine);
			const SA::FoldLevel levelParentLine = wEditor.FoldLevel(parentLine);
			wEditor.SetFoldExpanded(parentLine, true);
			ExpandFolds(parentLine, true, levelParentLine, wEditor);
		}

		if (!wEditor.FoldExpanded(line)) {
			// Removing the fold from one that has been contracted so should expand
			// otherwise lines are left invisible with no way to make them visible
			wEditor.SetFoldExpanded(line, true);
			if (!wEditor.AllLinesVisible())
				// Combining two blocks where the second one is collapsed (e.g. by adding characters in the line which separates the two blocks)
				ExpandFolds(line, true, levelPrev, wEditor);
		}
	}
	if (!LevelIsWhitespace(levelNow) &&	(LevelNumberPart(levelPrev) > LevelNumberPart(levelNow))) {
		if (!wEditor.AllLinesVisible()) {
			// See if should still be hidden
			const SA::Line parentLine = wEditor.FoldParent(line);
			if (parentLine < 0) {
				wEditor.ShowLines(line, line);
			} else if (wEditor.FoldExpanded(parentLine) && wEditor.LineVisible(parentLine)) {
				wEditor.ShowLines(line, line);
			}
		}
	}
	// Combining two blocks where the first one is collapsed (e.g. by adding characters in the line which separates the two blocks)
	if (!LevelIsWhitespace(levelNow) && (LevelNumberPart(levelPrev) < LevelNumberPart(levelNow))) {
		if (!wEditor.AllLinesVisible()) {
			const SA::Line parentLine = wEditor.FoldParent(line);
			if (!wEditor.FoldExpanded(parentLine) && wEditor.LineVisible(line)) {
				wEditor.SetFoldExpanded(parentLine, true);
				const SA::FoldLevel levelParentLine = wEditor.FoldLevel(parentLine);
				ExpandFolds(parentLine, true, levelParentLine, wEditor);
			}
		}
	}
}

void SciTEBase::ExpandFolds(SA::Line line, bool expand, SA::FoldLevel level, GUI::ScintillaWindow& wEditor) {
	// Expand or contract line and all subordinates
	// level is the fold level of line
	const SA::Line lineMaxSubord = wEditor.LastChild(line, LevelNumberPart(level));
	line++;
	wEditor.Call(expand ? SA::Message::ShowLines : SA::Message::HideLines, line, lineMaxSubord);
	while (line <= lineMaxSubord) {
		const SA::FoldLevel levelLine = wEditor.FoldLevel(line);
		if (LevelIsHeader(levelLine)) {
			wEditor.SetFoldExpanded(line, expand);
		}
		line++;
	}
}

void SciTEBase::FoldAll() {
	lEditor->Colourise(lEditor->EndStyled(), -1);
	const SA::Line maxLine = lEditor->LineCount();
	bool expanding = true;
	for (SA::Line lineSeek = 0; lineSeek < maxLine; lineSeek++) {
		if (LevelIsHeader(lEditor->FoldLevel(lineSeek))) {
			expanding = !lEditor->FoldExpanded(lineSeek);
			break;
		}
	}
	lEditor->SetRedraw(false);
	for (SA::Line line = 0; line < maxLine; line++) {
		const SA::FoldLevel level = lEditor->FoldLevel(line);
		if (LevelIsHeader(level) &&
				(SA::FoldLevel::Base == LevelNumberPart(level))) {
			const SA::Line lineMaxSubord = lEditor->LastChild(line, static_cast<SA::FoldLevel>(-1));
			if (expanding) {
				lEditor->SetFoldExpanded(line, true);
				ExpandFolds(line, true, level, *lEditor);
				line = lineMaxSubord;
			} else {
				lEditor->SetFoldExpanded(line, false);
				if (lineMaxSubord > line)
					lEditor->HideLines(line + 1, lineMaxSubord);
			}
		}
	}
	lEditor->SetRedraw(true);
}

void SciTEBase::GotoLineEnsureVisible(SA::Line line) {
	lEditor->EnsureVisibleEnforcePolicy(line);
	lEditor->GotoLine(line);
}

void SciTEBase::EnsureRangeVisible(GUI::ScintillaWindow &win, SA::Span range, bool enforcePolicy) {
	const SA::Line lineStart = win.LineFromPosition(range.start);
	const SA::Line lineEnd = win.LineFromPosition(range.end);
	for (SA::Line line = lineStart; line <= lineEnd; line++) {
		win.Call(enforcePolicy ? SA::Message::EnsureVisibleEnforcePolicy : SA::Message::EnsureVisible, line);
	}
}

bool SciTEBase::MarginClick(SA::Position position, int modifiers) {
	const SA::Line lineClick = lEditor->LineFromPosition(position);
	const SA::KeyMod km = static_cast<SA::KeyMod>(modifiers);
	if ((FlagIsSet(km, SA::KeyMod::Shift)) && (FlagIsSet(km, SA::KeyMod::Ctrl))) {
		FoldAll();
	} else {
		const SA::FoldLevel levelClick = lEditor->FoldLevel(lineClick);
		if (LevelIsHeader(levelClick)) {
			if (FlagIsSet(km, SA::KeyMod::Shift)) {
				EnsureAllChildrenVisible(lineClick, levelClick);
			} else if (FlagIsSet(km, SA::KeyMod::Ctrl)) {
				ToggleFoldRecursive(lineClick, levelClick, *lEditor);
			} else {
				// Toggle this line
				lEditor->ToggleFold(lineClick);
			}
		}
	}
	return true;
}

void SciTEBase::ToggleFoldRecursive(SA::Line line, SA::FoldLevel level, GUI::ScintillaWindow &wEditor) {
	if (wEditor.FoldExpanded(line)) {
		// This ensure fold structure created before the fold is expanded
		wEditor.LastChild(line, LevelNumberPart(level));
		// Contract this line and all children
		wEditor.SetFoldExpanded(line, false);
		ExpandFolds(line, false, level, wEditor);
	} else {
		// Expand this line and all children
		wEditor.SetFoldExpanded(line, true);
		ExpandFolds(line, true, level, wEditor);
	}
}

void SciTEBase::EnsureAllChildrenVisible(SA::Line line, SA::FoldLevel level) {
	// Ensure all children visible
	lEditor->SetFoldExpanded(line, true);
	ExpandFolds(line, true, level, *lEditor);
}

void SciTEBase::NewLineInOutput() {
	if (jobQueue.IsExecuting())
		return;
	SA::Line line = wOutput.LineFromPosition(wOutput.CurrentPos()) - 1;
	// Create command list from file and show it on output
	if (commandComandList)
	{
		FindFunctions();
		wOutput.GotoLine(line);
		DoGoToFoundFunc = PrevFVLiO;
		GoToFoundFunc();
		return;
	}
	std::string cmd = GetLine(wOutput, line);
	if (cmd == ">") {
		// Search output buffer for previous command
		line--;
		while (line >= 0) {
			cmd = GetLine(wOutput, line);
			if (cmd.starts_with(">") && !cmd.starts_with(">Exit")) {
				cmd = cmd.substr(1);
				break;
			}
			line--;
		}
	} else if (cmd.starts_with(">")) {
		cmd = cmd.substr(1);
	}
	returnOutputToCommand = false;
	AddCommand(cmd, "", JobSubsystem::cli);
	Execute();
}

// Подсветить функцию в которой сейчас находимся
void SciTEBase::HighlightFoundFunc(Sci_Position wELine, bool update) {
	if (!commandComandList) return;
	if (funcLineNumbers.empty()) return;
	if (!wELine) wELine = lEditor->LineFromPosition(lEditor->CurrentPos());
	auto it = std::upper_bound(funcLineNumbers.begin(), funcLineNumbers.end(), wELine);
	if (it == funcLineNumbers.begin()) return;
	--it;
	if (it == funcLineNumbers.end()) return;
	Sci_Position foundIdx = std::distance(funcLineNumbers.begin(), it);
	static Sci_Position lastHighlightedOutputLine = -1;
	if (foundIdx == lastHighlightedOutputLine && !update) return;
	lastHighlightedOutputLine = foundIdx;
	wOutput.GotoLine(foundIdx);
	if (DoGoToFoundFunc != -1) {
		wOutput.SetFirstVisibleLine(DoGoToFoundFunc);
		DoGoToFoundFunc = -1;
	}
	Sci_Position startPos = wOutput.PositionFromLine(foundIdx);
	Sci_Position endPos = wOutput.PositionFromLine(foundIdx + 1);
	wOutput.SetSel(startPos, endPos);
}

// Переход на выбранную функцию
void SciTEBase::GoToFoundFunc() {
	if (!commandComandList) return;

	Sci_Position clickedLineInOutput = wOutput.LineFromPosition(wOutput.CurrentPos());
	if (clickedLineInOutput < static_cast<Sci_Position>(funcLineNumbers.size())) {
		SA::Line targetLine = funcLineNumbers[clickedLineInOutput];
		lEditor->GotoLine(targetLine);
		lEditor->VerticalCentreCaret();
		lEditor->SetFocus(true);
	}
}

// Поиск функций AHK
void SciTEBase::FindFunctions() {
	if (!commandComandList)  return;
	PrevFVLiO = wOutput.FirstVisibleLine();


	// Выносим список исключений (blacklist)
	static const std::vector<std::string> blacklist = { "if", "else", "and", "or", "while", "for", "loop", "switch", "catch", "try" ,"return"};

	Sci_Position lineCount = wEditor.LineCount();
	if (lineCount <= 0) return;

	wOutput.SetRedraw(false);
	wOutput.ClearAll();
	funcLineNumbers.clear();
	std::string lineBuffer; // Один буфер на все итерации

	for (Sci_Position i = 0; i < lineCount; i++) {
		Sci_Position lineLen = wEditor.LineLength(i);
		if (lineLen <= 2) continue; // Пропускаем совсем пустые (1 - это \n)

		// 1. Получаем строку в буфер без лишних аллокаций
		lineBuffer.assign(lineLen, '\0');
		wEditor.GetLine(i, &lineBuffer[0]);

		// Используем string_view для анализа без копирования
		std::string_view sv(lineBuffer.c_str(), lineLen);

		size_t nameStart = sv.find_first_not_of(" \t");
		size_t wordEnd = sv.find_first_of(" \t\r\n", nameStart);
		std::string_view firstWord = sv.substr(nameStart, (wordEnd == std::string_view::npos) ? (sv.length() - nameStart) : (wordEnd - nameStart));

		if (firstWord.length() > 1 && firstWord.front() == ':') {
			int ColonCount = 0;
			for (size_t k = 0; k < firstWord.length(); ++k) {
				unsigned char c = static_cast<unsigned char>(firstWord[k]);
				if (c == ':') {
					ColonCount++;
				}
			}
			if (ColonCount >= 2) {
				AddToFunctionList(i, lineBuffer);
				continue;
			}
		}

		if (firstWord.length() > 1 && firstWord.back() == ':') {
			bool isLabel = true;
			for (size_t k = 0; k < firstWord.length() - 1; ++k) {
				unsigned char c = static_cast<unsigned char>(firstWord[k]);
				if (!isalnum(c) && c != '_' && !strchr(":~$*^!#", c)) {
					isLabel = false; break;
				}
			}
			if (isLabel) {
				size_t colonPos = nameStart + firstWord.length()-1;
				size_t afterсolonPos = sv.find_first_not_of(" \t\r\n", colonPos + 1);

				bool isTrueLabel = true;
				if (afterсolonPos != std::string_view::npos) {
					unsigned char ch = static_cast<unsigned char>(sv[afterсolonPos]);
					if (ch != ':' && ch != ';') {
						isTrueLabel = false;
					}
				}

				if (isTrueLabel) {
					AddToFunctionList(i, lineBuffer);
					continue;
				}
			}
		}

		if (CompareNoCase(std::string(firstWord).c_str(), "class") == 0) {
			AddToFunctionList(i, lineBuffer);
			continue;
		}

		// 2. Быстрый первичный фильтр
		size_t bracketOpen = sv.find('(');
		if (bracketOpen == std::string_view::npos || bracketOpen == 0) continue;

		size_t nameEnd = sv.find_last_not_of(" \t", bracketOpen - 1);

		if (nameStart == std::string_view::npos || nameStart >= bracketOpen) continue;

		std::string_view funcName = sv.substr(nameStart, nameEnd - nameStart + 1);
		// Проверка на разрешенные символы через isalnum (быстрее find_first_not_of)
		bool isValid = true;
		for (char c : funcName) {
			if (!isalnum(static_cast<unsigned char>(c)) && c != '_') {
				isValid = false; break;
			}
		}
		if (!isValid) continue;

		// Проверка черного списка (if, while...)
		bool isKeyword = false;
		for (const auto& word : blacklist) {
			if (CompareNoCase(std::string(funcName).c_str(), word.c_str()) == 0) {
				isKeyword = true; break;
			}
		}
		if (isKeyword) continue;

		// 4. Поиск открывающей скобки { (до 10 строк вперед)
		bool foundBrace = false;
		Sci_Position iShift = 0;

		bool lastChance = false;
		std::string nextBuffer;
		for (int j = 0; j < 10 && (i + j) < lineCount; j++) {
			Sci_Position nextLen = wEditor.LineLength(i + j);
			if (nextLen <= 0) break;

			nextBuffer.assign(nextLen + 1, '\0');
			wEditor.GetLine(i + j, &nextBuffer[0]);
			std::string_view nsv(nextBuffer.c_str(), nextLen);

			size_t firstIdx = nsv.find_first_not_of(" \t\r\n");
			if (firstIdx == std::string_view::npos) {
				if (nextLen <= 2) break;
				else continue;
			}
			// Если нашли { в начале строки
			if (nsv[firstIdx] == '{') {
				foundBrace = true; iShift = j; break;
			}

			// Если встретили } в начале - это не функция
			if (nsv[firstIdx] == '}') break;

			// Ищем { после закрывающей скобки )
			size_t bClose = nsv.rfind(')');
			if (bClose != std::string_view::npos) {
				size_t afterClose = nsv.find_first_not_of(" \t\r\n", bClose + 1);
				if (afterClose != std::string_view::npos && nsv[afterClose] == '{') {
					foundBrace = true; iShift = j; break;
				}
			}

			// Ищем конец слова. Разделителями считаем пробелы, скобки, точки, запятые и т.д.
			wordEnd = nsv.find_first_of(" \t\r\n(){}[],.:;+-*/", firstIdx);
			// Извлекаем слово (если разделитель не найден, берем всё до конца строки)
			firstWord = nsv.substr(firstIdx, (wordEnd == std::string_view::npos) ? wordEnd : (wordEnd - firstIdx));
			// Теперь вы можете проверять это слово. Например:
			isKeyword = false;
			for (const auto& word : blacklist) {
				if (CompareNoCase(std::string(firstWord).c_str(), word.c_str()) == 0) {
					isKeyword = true; break;
				}
			}
			if (isKeyword) break;

			// Если ничего не нашли, смотрим была ли запятая. Если небыло, то следующая строка последний шанс найти функцию.
			if (lastChance) break;
			size_t isThereComma = nsv.find(',');
			if (j > 0 && isThereComma == std::string_view::npos) lastChance = true;
		}

		if (foundBrace) {
			AddToFunctionList(i, lineBuffer);
			i += iShift;
		}
	}
	wOutput.AppendText(1, "\n");
	wOutput.SetFirstVisibleLine(PrevFVLiO);
	wOutput.SetRedraw(true);
}
void SciTEBase::AddToFunctionList(Sci_Position lineIndex, const std::string& text) {
	funcLineNumbers.push_back(lineIndex);
	std::string outMsg = std::to_string(lineIndex + 1) + ": " + text;
	wOutput.AppendText(static_cast<int>(outMsg.length()), outMsg.c_str());
}

void SciTEBase::UpdateUI(const SCNotification *notification) {
	const bool handled = extender && extender->OnUpdateUI();
	if (!handled) {
		BraceMatch(notification->nmhdr.idFrom == IDM_SRCWIN);
		if (notification->nmhdr.idFrom == IDM_SRCWIN) {
			UpdateStatusBar(false);
		}
		CheckMenusClipboard();
	}
	if (CurrentBuffer()->findMarks == Buffer::FindMarks::modified) {
		RemoveFindMarks();
	}
	const SA::Update updated = static_cast<SA::Update>(notification->updated);

	bool isSourceEditor = (notification->nmhdr.idFrom == IDM_SRCWIN || notification->nmhdr.idFrom == IDM_SRCWIN2);
	bool isFocusEditor = (pwFocussed == &wEditor || pwFocussed == &wEditor2);
	if (FlagIsSet(updated, SA::Update::Selection) || FlagIsSet(updated, SA::Update::Content)) {
		if (isSourceEditor == isFocusEditor) {
			// Only highlight focused pane.
			if (FlagIsSet(updated, SA::Update::Selection)) {
				currentWordHighlight.statesOfDelay = CurrentWordHighlight::StatesOfDelay::noDelay; // Selection has just been updated, so delay is disabled.
				currentWordHighlight.textHasChanged = false;
				HighlightCurrentWord(true);
			}
			else if (currentWordHighlight.textHasChanged) {
				HighlightCurrentWord(false);
			}
			if (commandComandList)
			{
				SA::Line line = lEditor->LineFromPosition(lEditor->CurrentPos());
				static Sci_Position lastLine = -1;
				if (line != lastLine) {
					lastLine = line;
					HighlightFoundFunc(line);
				}
			}
		}
		if ((notification->nmhdr.idFrom == IDM_MAPWIN)) {
			static Sci_Position lastmPos = -1;
			static bool fistMarkSync = true;
			SA::Line mline = wMarkerMap.LineFromPosition(wMarkerMap.CurrentPos());
			if (mline != lastmPos) {
				lastmPos = mline;

				if (!fistMarkSync) {
					SyncMarkersToMap();
					JumpToMarkerMap(mline);
					lEditor->SetFocus(true);
				}
				fistMarkSync = false;
			}
		}
		if (FlagIsSet(updated, SA::Update::Content) and !timerMapFix and isSourceEditor == isFocusEditor) {
			// Устанавливаем таймер на 1000 мс. 
			// Если таймер с таким ID уже запущен, он просто сбросится на начало (эффект Debounce)
			::SetTimer(static_cast<HWND>(wSciTE.GetID()), TIMER_ID_MAP_UPDATE, 1000, NULL);
		}
		else if (timerMapFix) timerMapFix--;
	}
	if (isSourceEditor == isFocusEditor and FlagIsSet(updated, SA::Update::VScroll)) {
		UpdateMapThumb();
		// Отменить скроллинг окна карты
		if (wMarkerMap.FirstVisibleLine() != 0) {
			wMarkerMap.SetFirstVisibleLine(0);
		}
	}
}

void SciTEBase::SetCanUndoRedo(bool canUndo_, bool canRedo_) {
	if (canUndo != canUndo_) {
		EnableAMenuItem(IDM_UNDO, canUndo_);
		canUndo = canUndo_;
	}
	if (canRedo != canRedo_) {
		EnableAMenuItem(IDM_REDO, canRedo_);
		canRedo = canRedo_;
	}
}

void SciTEBase::CheckCanUndoRedo() {
	bool canUndoNow = true;
	bool canRedoNow = true;
	if (lEditor->HasFocus()) {
		canUndoNow = lEditor->CanUndo();
		canRedoNow = lEditor->CanRedo();
	} else if (wOutput.HasFocus()) {
		canUndoNow = wOutput.CanUndo();
		canRedoNow = wOutput.CanRedo();
	}
	SetCanUndoRedo(canUndoNow, canRedoNow);
}

void SciTEBase::Modified(const SCNotification *notification) {
	const SA::ModificationFlags modificationType =
		static_cast<SA::ModificationFlags>(notification->modificationType);
	const bool textWasModified = FlagIsSet(modificationType, SA::ModificationFlags::InsertText) ||
		FlagIsSet(modificationType, SA::ModificationFlags::DeleteText);
	bool isSourceEditor = (notification->nmhdr.idFrom == IDM_SRCWIN || notification->nmhdr.idFrom == IDM_SRCWIN2);
	bool isFocusEditor = (pwFocussed == &wEditor || pwFocussed == &wEditor2);
	if (isSourceEditor && textWasModified)
		CurrentBuffer()->DocumentModified();
	if (FlagIsSet(modificationType, SA::ModificationFlags::LastStepInUndoRedo)) {
		// When the user hits undo or redo, several normal insert/delete
		// notifications may fire, but we will end up here in the end
		CheckCanUndoRedo();
	} else if (textWasModified) {
		if (isSourceEditor == isFocusEditor) {
			currentWordHighlight.textHasChanged = true;
		}
		// This will be called a lot, and usually means "typing".
		SetCanUndoRedo(true, false);
		if (CurrentBuffer()->findMarks == Buffer::FindMarks::marked) {
			CurrentBuffer()->findMarks = Buffer::FindMarks::modified;
		}
	}

	if (notification->linesAdded && lineNumbers && lineNumbersExpand) {
		SetLineNumberWidth();
	}

	if (FlagIsSet(modificationType, SA::ModificationFlags::ChangeFold)) {
		FoldChanged(notification->line,
			    static_cast<SA::FoldLevel>(notification->foldLevelNow),
			    static_cast<SA::FoldLevel>(notification->foldLevelPrev), wEditor);
		FoldChanged(notification->line,
			static_cast<SA::FoldLevel>(notification->foldLevelNow),
			static_cast<SA::FoldLevel>(notification->foldLevelPrev), wEditor2);
	}
}

bool SciTEBase::wMarkerMapInit() {
	wMarkerMap.SetReadOnly(false);
	wMarkerMap.ClearAll();

	std::string EmptyLine;
	EmptyLine.assign(MarkMapW/4-1, ' ');
	EmptyLine = EmptyLine + "\n";

	for (int i = 0; i < 3000; ++i) { // Количество однопиксельных строк
		wMarkerMap.AddText(EmptyLine.size(), EmptyLine.data());
	}
	wMarkerMap.SetReadOnly(true);
	return true;
}

// Добавить маркеры закладок на карту маркеров
void SciTEBase::SyncMarkersToMap() {
	static bool initw = wMarkerMapInit();
	static const int arrowH = ::GetSystemMetrics(SM_CYVSCROLL);
	static const int minThumbH = ::GetSystemMetrics(SM_CYVTHUMB);
	wMarkerMap.SetRedraw(false);
	GUI::ScintillaWindow* editors[] = { &wEditor, &wEditor2 };
	struct MarkMap { int mapMark; int editorMark; };
	MarkMap markerTypes[] = {
		{ MarkBookMarks, markerBookmark },
		{ MarkUserBookMarks, markerUserBookmark }
	};
	for (const auto& m : markerTypes) {
		wMarkerMap.MarkerDeleteAll(m.mapMark);
	}
	int currentYOffset = 0;
	for (int i = 0; i < 2; ++i) {
		GUI::ScintillaWindow& w = *editors[i];
		SCROLLINFO si = { sizeof(si), SIF_ALL };
		if (!::GetScrollInfo(static_cast<HWND>(w.GetID()), SB_VERT, &si) ||
			si.nPage <= 0 || si.nMax <= 0 || si.nMin == si.nMax)
		{
			currentYOffset += w.GetClientPosition().Height() + heightBar;
			continue;
		}
		const int windowHeight = w.GetClientPosition().Height();
		int trackH = windowHeight - (arrowH * 2);
		if (trackH < minThumbH) trackH = minThumbH;
		const double scrollRange = static_cast<double>(si.nMax - si.nMin);
		const int thumbH = static_cast<int>((static_cast<double>(si.nPage) * trackH) / scrollRange);
		int rows = (thumbH + si.nPage - 1) / si.nPage;
		if (rows < 2) rows = 2;
		for (const auto& m : markerTypes) {
			Sci_Position lineWithMarker = wEditor.MarkerNext(0, (1 << m.editorMark));
			while (lineWithMarker != -1) {
				const Sci_Position displayLine = w.VisibleFromDocLine(lineWithMarker);
				const double ratio = static_cast<double>(displayLine) / scrollRange;
				const int targetMapLine = currentYOffset + arrowH + static_cast<int>(ratio * trackH);
				for (int r = 0; r < rows; r++) {
					wMarkerMap.MarkerAdd(targetMapLine + r, m.mapMark);
				}
				lineWithMarker = wEditor.MarkerNext(lineWithMarker + 1, (1 << m.editorMark));
			}
		}
		currentYOffset += windowHeight + heightBar;
	}

	wMarkerMap.SetFirstVisibleLine(0);
	wMarkerMap.SetRedraw(true);
}

// Перейти на позицию на карте маркеров
void SciTEBase::JumpToMarkerMap(Sci_Position mapLine) {
	int windowHeight = wEditor.GetClientPosition().Height();
	SCROLLINFO si = { sizeof(si), SIF_RANGE | SIF_PAGE };
	GUI::ScintillaWindow* Editor = &wEditor;
	SA::Position clkpos = wMarkerMap.PositionFromLine(mapLine);
	wMarkerMap.SetSel(clkpos, clkpos);
	if (mapLine > windowHeight + heightBar) {
		mapLine -= windowHeight + heightBar;
		Editor = &wEditor2;
	}

	if (!::GetScrollInfo(static_cast<HWND>(Editor->GetID()), SB_VERT, &si)) return;
	if (si.nPage <= 0) return;
	if (si.nMax <= 0) return;
	if (si.nMin == si.nMax) return;
	windowHeight = Editor->GetClientPosition().Height();
	const int arrowH = ::GetSystemMetrics(SM_CYVSCROLL);
	int trackH = windowHeight - (arrowH * 2);
	if (trackH <= 0) return;

	double ratio = static_cast<double>(mapLine - arrowH) / trackH;

	if (ratio < 0.0) ratio = 0.0;
	if (ratio > 1.0) ratio = 1.0;
	Sci_Position targetDisplayLine = static_cast<Sci_Position>(ratio * si.nMax);
	Sci_Position targetDocLine = Editor->DocLineFromVisible(targetDisplayLine);

	Editor->GotoLine(targetDocLine);
	Editor->VerticalCentreCaret();
	Editor->SetFocus(true);
}

// Обновляет отображение ползунков на карте маркеров
void SciTEBase::UpdateMapThumb() {
	static const int arrowH = ::GetSystemMetrics(SM_CYVSCROLL);
	wMarkerMap.MarkerDeleteAll(MarkScrollBar);
	GUI::ScintillaWindow* editors[] = { &wEditor, &wEditor2 };
	int currentYOffset = 0;
	for (int i = 0; i < 2; ++i) {
		GUI::ScintillaWindow& w = *editors[i];
		SCROLLINFO si = { sizeof(si), SIF_ALL };
		if (!::GetScrollInfo(static_cast<HWND>(w.GetID()), SB_VERT, &si) ||
			si.nPage <= 0 || si.nMax <= 0 || si.nMin == si.nMax)
		{
			currentYOffset += w.GetClientPosition().Height() + heightBar;
			continue;
		}
		const int windowHeight = w.GetClientPosition().Height();
		const int lineHeight = w.StyleGetSize(32);
		if (lineHeight <= 0) continue;
		const Sci_Position firstLine = w.FirstVisibleLine();
		const int trackH = windowHeight - (arrowH * 2);
		const double scrollRange = static_cast<double>(si.nMax - si.nMin);
		const double ratioStart = static_cast<double>(firstLine) / scrollRange;
		int thumbH = static_cast<int>((static_cast<double>(si.nPage) * trackH) / scrollRange);
		if (thumbH < 1) thumbH = 1;
		const int mapStartLine = currentYOffset + arrowH + static_cast<int>(ratioStart * trackH);
		for (int j = mapStartLine; j <= mapStartLine + thumbH; ++j) {
			wMarkerMap.MarkerAdd(j, MarkScrollBar);
		}
		currentYOffset += windowHeight + heightBar;
	}
	wMarkerMap.MarkerDeleteAll(MarkSplitter);
	const int windowH = wEditor.GetClientPosition().Height();
	for (int j = windowH; j <= windowH + heightBar; ++j) {
		wMarkerMap.MarkerAdd(j, MarkSplitter);
	}
}

// Добавляет маркеры истории на карту маркеров
void SciTEBase::ReadHistory() {
	static const int arrowH = ::GetSystemMetrics(SM_CYVSCROLL);
	static const int minThumbH = ::GetSystemMetrics(SM_CYVTHUMB);
	wMarkerMap.SetRedraw(false);
	wEditor2.SetRedraw(false);
	constexpr size_t markerHistory = static_cast<size_t>(SA::MarkerOutline::HistoryRevertedToOrigin);
	for (int i = 0; i < 4; ++i) {
		wMarkerMap.MarkerDeleteAll(MarkScrollHis + i);
		wEditor2.MarkerDeleteAll(markerHistory + i);
	}
	GUI::ScintillaWindow* editors[] = { &wEditor, &wEditor2 };
	int currentYOffset = 0;

	for (int i = 0; i < 2; ++i) {
		GUI::ScintillaWindow& w = *editors[i];
		SCROLLINFO si = { sizeof(si), SIF_ALL };

		if (!::GetScrollInfo(static_cast<HWND>(w.GetID()), SB_VERT, &si) ||
			si.nPage <= 0 || si.nMax <= 0 || si.nMin == si.nMax)
		{
			currentYOffset += w.GetClientPosition().Height() + heightBar;
			continue;
		}

		const int windowHeight = w.GetClientPosition().Height();
		int trackH = windowHeight - (arrowH * 2);
		if (trackH < minThumbH) trackH = minThumbH;

		const double scrollRange = static_cast<double>(si.nMax - si.nMin);
		const int thumbH = static_cast<int>((static_cast<double>(si.nPage) * trackH) / scrollRange);
		int rows = (thumbH + si.nPage - 1) / si.nPage;
		if (rows < 2) rows = 2;

		const int lineCount = w.LineCount();

		for (SA::Line lineDoc = 0; lineDoc < lineCount; ++lineDoc) {
			const unsigned int mask = static_cast<unsigned int>(wEditor.MarkerGet(lineDoc));
			int historyMarkerOnMap = 0, wE2His = 0;
			if (mask & (1 << 21))      historyMarkerOnMap = MarkScrollHis + 0, wE2His = markerHistory + 0;
			else if (mask & (1 << 22)) historyMarkerOnMap = MarkScrollHis + 1, wE2His = markerHistory + 1;
			else if (mask & (1 << 23)) historyMarkerOnMap = MarkScrollHis + 2, wE2His = markerHistory + 2;
			else if (mask & (1 << 24)) historyMarkerOnMap = MarkScrollHis + 3, wE2His = markerHistory + 3;

			if (historyMarkerOnMap != 0) {
				const double ratio = static_cast<double>(w.VisibleFromDocLine(lineDoc)) / scrollRange;
				const int targetMapLine = currentYOffset + arrowH + static_cast<int>(ratio * trackH);
				for (int r = 0; r < rows; r++) {
					wMarkerMap.MarkerAdd(targetMapLine + r, historyMarkerOnMap);
				}
				if (i==0) wEditor2.MarkerAdd(lineDoc, wE2His);
			}
		}
		currentYOffset += windowHeight + heightBar;
	}
	wMarkerMap.SetRedraw(true);
	wEditor2.SetRedraw(true);
}

void SciTEBase::Notify(SCNotification *notification) {
	bool handled = false;
	bool isSourceEditor = (notification->nmhdr.idFrom == IDM_SRCWIN || notification->nmhdr.idFrom == IDM_SRCWIN2);
	bool isFocusEditor = (pwFocussed == &wEditor || pwFocussed == &wEditor2);
	switch (static_cast<SA::Notification>(notification->nmhdr.code)) {
	case SA::Notification::Painted:
		if (isSourceEditor == isFocusEditor) {
		//if ((notification->nmhdr.idFrom == IDM_SRCWIN) == (pwFocussed == &wEditor)) {
			// Only highlight focused pane.
			// Manage delay before highlight when no user selection but there is word at the caret.
			// So the Delay is based on the blinking of caret, scroll...
			// If currentWordHighlight.statesOfDelay == currentWordHighlight.delay,
			// then there is word at the caret without selection, and need some delay.
			if (currentWordHighlight.statesOfDelay == CurrentWordHighlight::StatesOfDelay::delay) {
				if (currentWordHighlight.elapsedTimes.Duration() >= 0.5) {
					currentWordHighlight.statesOfDelay = CurrentWordHighlight::StatesOfDelay::delayJustEnded;
					HighlightCurrentWord(true);
					pwFocussed->InvalidateAll();
				}
			}
		}
		break;

	case SA::Notification::FocusIn:
		//SetPaneFocus(notification->nmhdr.idFrom == IDM_SRCWIN);
		if (notification->nmhdr.idFrom == IDM_SRCWIN) {
			pwFocussed = &wEditor;
			lEditor = &wEditor;
		} else if (notification->nmhdr.idFrom == IDM_SRCWIN2) {
			pwFocussed = &wEditor2;
			lEditor = &wEditor2;
		} else {
			pwFocussed = &wOutput;
		}
		CheckMenus();
		break;

	case SA::Notification::FocusOut:
		CheckMenus();
		break;

	case SA::Notification::StyleNeeded: {
			if (extender) {
				// Colourisation may be performed by script
				if (isSourceEditor && (lexLanguage == SCLEX_CONTAINER)) {
					SA::Position endStyled = lEditor->EndStyled();
					const SA::Line lineEndStyled = lEditor->LineFromPosition(endStyled);
					endStyled = lEditor->LineStart(lineEndStyled);
					StyleWriter styler(*lEditor);
					int styleStart = 0;
					if (endStyled > 0)
						styleStart = styler.StyleAt(endStyled - 1);
					styler.SetCodePage(codePage);
					extender->OnStyle(endStyled, notification->position - endStyled,
							  styleStart, &styler);
					styler.Flush();
				}
			}
		}
		break;

	case SA::Notification::CharAdded:
		if (extender)
			handled = extender->OnChar(static_cast<char>(notification->ch));
		if (!handled) {
			if (isSourceEditor) {
				CharAdded(notification->ch);
			} else {
				CharAddedOutput(notification->ch);
			}
		}
		break;

	case SA::Notification::SavePointReached:
		if (isSourceEditor) {
			if (extender)
				handled = extender->OnSavePointReached();
			if (!handled) {
				CurrentBuffer()->isDirty = false;
			}
		}
		CheckMenus();
		SetWindowName();
		SetBuffersMenu();
		break;

	case SA::Notification::SavePointLeft:
		if (isSourceEditor) {
			if (extender)
				handled = extender->OnSavePointLeft();
			if (!handled) {
				CurrentBuffer()->isDirty = true;
				jobQueue.isBuilt = false;
			}
		}
		CheckMenus();
		SetWindowName();
		SetBuffersMenu();
		break;

	case SA::Notification::DoubleClick:
		if (extender)
			handled = extender->OnDoubleClick();
		if (!handled && notification->nmhdr.idFrom == IDM_RUNWIN) {
			if (commandComandList)
			{
				SA::Line line = wOutput.LineFromPosition(wOutput.CurrentPos());
				FindFunctions();
				DoGoToFoundFunc = PrevFVLiO;
				wOutput.GotoLine(line);
				GoToFoundFunc();
			}
			else {
				GoMessage(0);
			}
		}
		break;

	case SA::Notification::UpdateUI:
		UpdateUI(notification);
		break;

	case SA::Notification::Modified:
		Modified(notification);
		break;

	case SA::Notification::MarginClick: {
			if (extender)
				handled = extender->OnMarginClick();
			if (!handled && notification->nmhdr.idFrom == IDM_MAPWIN) {
				SyncMarkersToMap();
				SA::Line line = wMarkerMap.LineFromPosition(wMarkerMap.CurrentPos());
				JumpToMarkerMap(line);
			}
			else if (!handled) {
				if (notification->margin == 1) {
					SA::Line line = (lEditor->LineFromPosition(notification->position));
					BookmarkToggle(line);
					SyncMarkersToMap();
				}
				if (notification->margin == 2) {
					MarginClick(notification->position, notification->modifiers);
				}
			}
		}
		break;

	case SA::Notification::NeedShown: {
			EnsureRangeVisible(*lEditor, SA::Span(notification->position, notification->position + notification->length), false);
		}
		break;

	case SA::Notification::UserListSelection: {
			if (notification->wParam == 2)
				ContinueMacroList(notification->text);
			else if (extender && notification->wParam > 2)
				extender->OnUserListSelection(static_cast<int>(notification->wParam), notification->text);
		}
		break;

	case SA::Notification::CallTipClick: {
			if (notification->position == 1 && currentCallTip > 0) {
				currentCallTip--;
				FillFunctionDefinition();
			} else if (notification->position == 2 && currentCallTip + 1 < maxCallTips) {
				currentCallTip++;
				FillFunctionDefinition();
			}
		}
		break;

	case SA::Notification::MacroRecord:
		RecordMacroCommand(notification);
		break;

	case SA::Notification::URIDropped:
		OpenUriList(notification->text);
		break;

	case SA::Notification::DwellStart:
		if (extender && (SA::InvalidPosition != notification->position)) {
			SA::Span range(notification->position);
			std::string message =
				RangeExtendAndGrab(*lEditor,
						   range, &SciTEBase::iswordcharforsel);
			if (message.length()) {
				extender->OnDwellStart(range.start, message.c_str());
			}
		}
		break;

	case SA::Notification::DwellEnd:
		if (extender) {
			extender->OnDwellStart(0, ""); // flags end of calltip
		}
		break;

	case SA::Notification::Zoom:
		SetLineNumberWidth();
		UpdateStatusBar(false);
		break;

	case SA::Notification::ModifyAttemptRO:
		AbandonAutomaticSave();
		break;

	default:
		// Avoid warning for unhandled enumeration for notifications SciTEBase not interested in
		break;
	}
}

void SciTEBase::CheckMenusClipboard() {
	const bool hasSelection = !CallFocusedElseDefault(false, SA::Message::GetSelectionEmpty);
	EnableAMenuItem(IDM_CUT, hasSelection);
	EnableAMenuItem(IDM_COPY, hasSelection);
	EnableAMenuItem(IDM_CLEAR, hasSelection);
	EnableAMenuItem(IDM_PASTE, CallFocusedElseDefault(true, SA::Message::CanPaste));
	EnableAMenuItem(IDM_SELECTALL, true);
}

void SciTEBase::CheckMenus() {
	CheckMenusClipboard();
	CheckCanUndoRedo();
	EnableAMenuItem(IDM_DUPLICATE, !CurrentBuffer()->isReadOnly);
	EnableAMenuItem(IDM_SHOWCALLTIP, apis != 0);
	EnableAMenuItem(IDM_COMPLETE, apis != 0);
	CheckAMenuItem(IDM_SPLITVERTICAL, splitVertical);
	EnableAMenuItem(IDM_OPENFILESHERE, props.GetInt("check.if.already.open") != 0);
	CheckAMenuItem(IDM_OPENFILESHERE, openFilesHere);
	CheckAMenuItem(IDM_WRAP, wrap);
	CheckAMenuItem(IDM_WRAPOUTPUT, wrapOutput);
	CheckAMenuItem(IDM_READONLY, CurrentBuffer()->isReadOnly);
	CheckAMenuItem(IDM_FULLSCREEN, fullScreen);
	CheckAMenuItem(IDM_VIEWTOOLBAR, tbVisible);
	CheckAMenuItem(IDM_VIEWTABBAR, tabVisible);
	CheckAMenuItem(IDM_VIEWSTATUSBAR, sbVisible);
	CheckAMenuItem(IDM_VIEWEOL, lEditor->ViewEOL());
	CheckAMenuItem(IDM_VIEWSPACE, lEditor->ViewWS() != SA::WhiteSpace::Invisible);
	CheckAMenuItem(IDM_VIEWGUIDES, lEditor->IndentationGuides() != SA::IndentView::None);
	CheckAMenuItem(IDM_LINENUMBERMARGIN, lineNumbers);
	CheckAMenuItem(IDM_SELMARGIN, margin);
	CheckAMenuItem(IDM_FOLDMARGIN, foldMargin);
	CheckAMenuItem(IDM_TOGGLEOUTPUT, heightOutput > heightBar);
	CheckAMenuItem(IDM_SPLITSCREEN, heightEditorSplit > heightBar);
	CheckAMenuItem(IDM_TOGGLEPARAMETERS, ParametersOpen());
	CheckAMenuItem(IDM_MONOFONT, CurrentBuffer()->useMonoFont);
	EnableAMenuItem(IDM_COMPILE, !jobQueue.IsExecuting() &&
			props.GetWild("command.compile.", FileNameExt().AsUTF8()).size() != 0);
	EnableAMenuItem(IDM_BUILD, !jobQueue.IsExecuting() &&
			props.GetWild("command.build.", FileNameExt().AsUTF8()).size() != 0);
	EnableAMenuItem(IDM_CLEAN, !jobQueue.IsExecuting() &&
			props.GetWild("command.clean.", FileNameExt().AsUTF8()).size() != 0);
	EnableAMenuItem(IDM_GO, !jobQueue.IsExecuting() &&
			props.GetWild("command.go.", FileNameExt().AsUTF8()).size() != 0);
	EnableAMenuItem(IDM_OPENDIRECTORYPROPERTIES, props.GetInt("properties.directory.enable") != 0);
	for (int toolItem = 0; toolItem < toolMax; toolItem++)
		EnableAMenuItem(IDM_TOOLS + toolItem, ToolIsImmediate(toolItem) || !jobQueue.IsExecuting());
	EnableAMenuItem(IDM_STOPEXECUTE, jobQueue.IsExecuting());
	if (buffers.size() > 0) {
		TabSelect(buffers.Current());
		for (int bufferItem = 0; bufferItem < buffers.lengthVisible; bufferItem++) {
			CheckAMenuItem(IDM_BUFFER + bufferItem, bufferItem == buffers.Current());
		}
	}
	EnableAMenuItem(IDM_MACROPLAY, !recording);
	EnableAMenuItem(IDM_MACRORECORD, !recording);
	EnableAMenuItem(IDM_MACROSTOPRECORD, recording);
	EnableAMenuItem(IDM_COM_LIST, commandComandList);
}

void SciTEBase::ContextMenu(GUI::ScintillaWindow &wSource, GUI::Point pt, GUI::Point ptClient, GUI::Window wCmd) {
	const SA::Position currentPos = wSource.CurrentPos();
	const SA::Position anchor = wSource.Anchor();
	contextSelection = wSource.SelectionFromPoint(ptClient.x, ptClient.y);
	const bool isStreamSelection = wSource.SelectionMode() == SA::SelectionMode::Stream;
	const bool allowDrop = isStreamSelection && (contextSelection >= 0);
	popup.CreatePopUp();
	const bool writable = !wSource.ReadOnly();
	AddToPopUp("Undo", IDM_UNDO, writable && wSource.CanUndo());
	AddToPopUp("Redo", IDM_REDO, writable && wSource.CanRedo());
	AddToPopUp("");
	AddToPopUp("Cut", IDM_CUT, writable && currentPos != anchor);
	AddToPopUp("Copy", IDM_COPY, currentPos != anchor);
	AddToPopUp("Paste", IDM_PASTE, writable && wSource.CanPaste());
	AddToPopUp("Delete", IDM_CLEAR, writable && currentPos != anchor);
	AddToPopUp("");
	AddToPopUp("Select All", IDM_SELECTALL);
	AddToPopUp("Drop Selection", IDM_DROPSELECTION, allowDrop);
	AddToPopUp("");
	if (wSource.GetID() == wOutput.GetID()) {
		AddToPopUp("Hide", IDM_TOGGLEOUTPUT, true);
	} else {
		AddToPopUp("&Clear All Bookmarks", IDM_BOOKMARK_CLEARALL, true);
		AddToPopUp("");
		AddToPopUp("&Code Page Property", IDM_ENCODING_DEFAULT, true);
		AddToPopUp("&UTF-8", IDM_ENCODING_UCOOKIE, true);
	}

	//POPUP "Encodin&g"
	//	BEGIN
	//	MENUITEM "&Code Page Property", IDM_ENCODING_DEFAULT
	//	MENUITEM "UTF-16 &Big Endian", IDM_ENCODING_UCS2BE
	//	MENUITEM "UTF-16 &Little Endian", IDM_ENCODING_UCS2LE
	//	MENUITEM "UTF-8 &with BOM", IDM_ENCODING_UTF8
	//	MENUITEM "&UTF-8", IDM_ENCODING_UCOOKIE
	//	END

	std::string userContextMenu = props.GetNewExpandString("user.context.menu");
	std::ranges::replace(userContextMenu, '|', '\0');
	const char *userContextItem = userContextMenu.c_str();
	const char *endDefinition = userContextItem + userContextMenu.length();
	while (userContextItem < endDefinition) {
		const char *caption = userContextItem;
		userContextItem += strlen(userContextItem) + 1;
		if (userContextItem < endDefinition) {
			const int cmd = GetMenuCommandAsInt(userContextItem);
			userContextItem += strlen(userContextItem) + 1;
			AddToPopUp(caption, cmd);
		}
	}
	popup.Show(pt, wCmd);
}

/**
 * Ensure that a splitter bar position is inside the main window.
 */
int SciTEBase::NormaliseSplit(int splitPos) {
	const GUI::Rectangle rcClient = GetClientRectangle();
	const int w = rcClient.Width();
	const int h = rcClient.Height();
	if (splitPos < heightBar)
		splitPos = heightBar;
	if (splitVertical) {
		if (splitPos > w - heightBar - minimumSplit)
			splitPos = w - heightBar;
	} else {
		if (splitPos > h - heightBar - minimumSplit)
			splitPos = h - heightBar;
	}
	return splitPos;
}
int SciTEBase::NormaliseESplit(int splitPos) {
	const GUI::Rectangle rcClient = GetClientRectangle();
	const int w = rcClient.Width();
	int h = rcClient.Height();
	if (splitPos < heightBar) splitPos = heightBar;
	if (!splitVertical) h -= heightOutput;
	if (splitPos > h / 3 * 2)
		splitPos = h / 3 * 2;
	return splitPos;
}

void SciTEBase::MoveSplit(GUI::Point ptNewDrag) {

	if (moveEditor2) {
		int newHeightwEditor2 = heightEditorStartDrag + (ptStartDrag.y - ptNewDrag.y);
		newHeightwEditor2 = NormaliseESplit(newHeightwEditor2);
		if (heightEditorSplit != newHeightwEditor2) {
			heightEditorSplit = newHeightwEditor2;
			SizeContentWindows();
			//Redraw();
		}

		previousHeightwEditor2 = newHeightwEditor2;
	}
	else {
		int newHeightOutput = heightOutputStartDrag + (ptStartDrag.y - ptNewDrag.y);
		if (splitVertical)
			newHeightOutput = heightOutputStartDrag - (ptStartDrag.x - ptNewDrag.x);
		newHeightOutput = NormaliseSplit(newHeightOutput);
		if (heightOutput != newHeightOutput) {
			heightOutput = newHeightOutput;
			SizeContentWindows();
			//Redraw();
		}

		previousHeightOutput = newHeightOutput;
	}
}

void SciTEBase::TimerStart(int /* mask */) {
}

void SciTEBase::TimerEnd(int /* mask */) {
}

void SciTEBase::OnTimer(uintptr_t  wParam) {
	if (wParam == TIMER_ID_MAP_UPDATE) {
		SyncMarkersToMap();
		UpdateMapThumb();
		ReadHistory();
		FindFunctions();
		SA::Line line = lEditor->LineFromPosition(lEditor->CurrentPos());
		HighlightFoundFunc(line, true);
		::KillTimer(static_cast<HWND>(wSciTE.GetID()), TIMER_ID_MAP_UPDATE);
		timerMapFix = 3;
		return;
	}
	if (delayBeforeAutoSave && (0 == dialogsOnScreen)) {
		// First save the visible buffer to avoid any switching if not needed
		if (CurrentBuffer()->NeedsSave(delayBeforeAutoSave)) {
			Save(sfNone);
		}
		// Then look through the other buffers to save any that need to be saved
		const BufferIndex currentBuffer = buffers.Current();
		for (BufferIndex i = 0; i < buffers.length; i++) {
			if (buffers.buffers[i].NeedsSave(delayBeforeAutoSave)) {
				SetDocumentAt(i);
				Save(sfNone);
			}
		}
		SetDocumentAt(currentBuffer);
	}
}

void SciTEBase::SetIdler(bool on) {
	needIdle = on;
}

void SciTEBase::OnIdle() {
	if (!findMarker.Complete()) {
		wEditor.SetRedraw(false);
		wEditor2.SetRedraw(false);
		findMarker.Continue();
		wEditor.SetRedraw(true);
		wEditor2.SetRedraw(true);
		return;
	}
	if (!matchMarker.Complete()) {
		matchMarker.Continue();
		return;
	}
	SetIdler(false);
}

void SciTEBase::SetHomeProperties() {
	props.SetPath("SciteDefaultHome", GetSciteDefaultHome());
	props.SetPath("SciteUserHome", GetSciteUserHome());
}

void SciTEBase::UIAvailable() {
	SetImportMenu();
	if (extender) {
		SetHomeProperties();
		extender->Initialise(this);
	}
}

namespace {

constexpr bool IsNameCharacter(GUI::gui_char ch) {
	return ch == '.' || IsAlphabetic(ch);
}

/**
 * Find the character following a name which is made up of characters from
 * the set [a-zA-Z.]
 */
GUI::gui_char AfterName(GUI::gui_string_view s) noexcept {
	while (!s.empty() && IsNameCharacter(s.front())) {
		s.remove_prefix(1);
	}
	return s.empty() ? 0 : s.front();
}

}

void SciTEBase::PerformOne(std::string_view action) {
	const size_t colon = action.find(':');
	if (colon != std::string::npos) {
		const std::string_view cmd = action.substr(0, colon);
		const std::string argument = UnSlashString(action.substr(colon+1));
		const char *arg = argument.c_str();
		if (cmd == "askfilename") {
			extender->OnMacro("filename", filePath.AsUTF8().c_str());
		} else if (cmd == "askproperty") {
			PropertyToDirector(arg);
		} else if (cmd == "close") {
			Close();
			WindowSetFocus(*lEditor);
		} else if (cmd == "currentmacro") {
			currentMacro = arg;
		} else if (cmd == "cwd") {
			FilePath dirTarget(GUI::StringFromUTF8(arg));
			if (!dirTarget.SetWorkingDirectory()) {
				GUI::gui_string msg = LocaliseMessage("Invalid directory '^0'.", dirTarget.AsInternal());
				WindowMessageBox(wSciTE, msg);
			}
		} else if (cmd == "enumproperties") {
			EnumProperties(arg);
		} else if (cmd == "exportashtml") {
			SaveToHTML(GUI::StringFromUTF8(arg));
		} else if (cmd == "exportasrtf") {
			SaveToRTF(GUI::StringFromUTF8(arg));
		} else if (cmd == "exportaspdf") {
			SaveToPDF(GUI::StringFromUTF8(arg));
		} else if (cmd == "exportaslatex") {
			SaveToTEX(GUI::StringFromUTF8(arg));
		} else if (cmd == "exportasxml") {
			SaveToXML(GUI::StringFromUTF8(arg));
		} else if (cmd == "find" && lEditor->Created()) {
			findWhat = arg;
			isFromButton = true;
			FindNext(false, false);
		} else if (cmd == "goto" && lEditor->Created()) {
			const SA::Line line = IntegerFromText(arg) - 1;
			GotoLineEnsureVisible(line);
			// jump to column if given and greater than 0
			const char *colstr = strchr(arg, ',');
			if (colstr) {
				const SA::Position col = IntegerFromText(colstr + 1);
				if (col > 0) {
					const SA::Position pos = lEditor->CurrentPos() + col;
					// select the word you have found there
					const SA::Position wordStart = lEditor->WordStartPosition(pos, true);
					const SA::Position wordEnd = lEditor->WordEndPosition(pos, true);
					lEditor->SetSel(wordStart, wordEnd);
				}
			}
		} else if (cmd == "insert" && lEditor->Created()) {
			lEditor->ReplaceSel(arg);
		} else if (cmd == "loadsession") {
			if (*arg) {
				LoadSessionFile(GUI::StringFromUTF8(arg).c_str());
				RestoreSession();
			}
		} else if (cmd == "macrocommand") {
			ExecuteMacroCommand(arg);
		} else if (cmd == "macroenable") {
			macrosEnabled = atoi(arg);
			SetToolsMenu();
		} else if (cmd == "macrolist") {
			StartMacroList(arg);
		} else if (cmd == "menucommand") {
			MenuCommand(atoi(arg));
		} else if (cmd == "open") {
			Open(GUI::StringFromUTF8(argument), ofSynchronous);
		} else if (cmd == "output" && wOutput.Created()) {
			wOutput.ReplaceSel(arg);
		} else if (cmd == "property") {
			PropertyFromDirector(arg);
		} else if (cmd == "reloadproperties") {
			ReloadProperties();
		} else if (cmd == "quit") {
			QuitProgram();
		} else if (cmd == "replaceall" && lEditor->Created()) {
			const size_t nulPos = argument.find('\0');
			if (nulPos != std::string::npos) {
				findWhat = argument.substr(0,nulPos);
				replaceWhat = argument.substr(nulPos+1);
				ReplaceAll(false);
			}
		} else if (cmd == "saveas") {
			if (*arg) {
				SaveAs(GUI::StringFromUTF8(arg).c_str(), true);
			} else {
				SaveAsDialog();
			}
		} else if (cmd == "savesession") {
			if (*arg) {
				SaveSessionFile(GUI::StringFromUTF8(arg).c_str());
			}
		} else if (cmd == "setdefaultcwd") {
			// This sets cwd to a value that should stay valid: either SciTE_HOME or the
			// SciTE installation directory or directory of SciTE executable.
			GetDefaultDirectory().SetWorkingDirectory();
		} else if (cmd == "extender") {
			extender->OnExecute(arg);
		} else if (cmd == "focus") {
			ActivateWindow(arg);
		}
	}
}

namespace {

constexpr bool IsSwitchCharacter(GUI::gui_char ch) noexcept {
#if defined(__unix__) || defined(__APPLE__)
	return ch == '-';
#else
	return (ch == '-') || (ch == '/');
#endif
}

}

// Called by SciTEBase::PerformOne when action="enumproperties:"
void SciTEBase::EnumProperties(const char *propkind) {
	const PropSetFile *pf = nullptr;

	if (!extender)
		return;
	if (!strcmp(propkind, "dyn")) {
		SelectionIntoProperties(); // Refresh properties ...
		pf = &props;
	} else if (!strcmp(propkind, "local"))
		pf = &propsLocal;
	else if (!strcmp(propkind, "directory"))
		pf = &propsDirectory;
	else if (!strcmp(propkind, "user"))
		pf = &propsUser;
	else if (!strcmp(propkind, "base"))
		pf = &propsBase;
	else if (!strcmp(propkind, "embed"))
		pf = &propsEmbed;
	else if (!strcmp(propkind, "platform"))
		pf = &propsPlatform;
	else if (!strcmp(propkind, "abbrev"))
		pf = &propsAbbrev;

	if (pf) {
		const char *key = nullptr;
		const char *val = nullptr;
		bool b = pf->GetFirst(key, val);
		while (b) {
			SendOneProperty(propkind, key, val);
			b = pf->GetNext(key, val);
		}
	}
}

void SciTEBase::SendOneProperty(const char *kind, const char *key, const char *val) {
	std::string m = kind;
	m += ":";
	m += key;
	m += "=";
	m += val;
	extender->SendProperty(m.c_str());
}

void SciTEBase::PropertyFromDirector(const char *arg) {
	props.SetLine(arg, false);
}

void SciTEBase::PropertyToDirector(std::string_view arg) {
	if (!extender)
		return;
	SelectionIntoProperties();
	const std::string gotprop = props.GetString(arg);
	extender->OnMacro("macro:stringinfo", gotprop.c_str());
}

/**
 * Menu/Toolbar command "Record".
 */
void SciTEBase::StartRecordMacro() {
	recording = true;
	CheckMenus();
	wEditor.StartRecord();
}

/**
 * Received a Notification::MacroRecord from Scintilla: send it to director.
 */
bool SciTEBase::RecordMacroCommand(const SCNotification *notification) {
	if (extender) {
		std::string sMessage = StdStringFromInteger(notification->message);
		sMessage += ";";
		sMessage += std::to_string(notification->wParam);
		sMessage += ";";
		const char *t = reinterpret_cast<const char *>(notification->lParam);
		if (t) {
			//format : "<message>;<wParam>;1;<text>"
			sMessage += "1;";
			sMessage += t;
		} else {
			//format : "<message>;<wParam>;0;"
			sMessage += "0;";
		}
		const bool handled = extender->OnMacro("macro:record", sMessage.c_str());
		return handled;
	}
	return true;
}

/**
 * Menu/Toolbar command "Stop recording".
 */
void SciTEBase::StopRecordMacro() {
	wEditor.StopRecord();
	if (extender)
		extender->OnMacro("macro:stoprecord", "");
	recording = false;
	CheckMenus();
}

/**
 * Menu/Toolbar command "Play macro...": tell director to build list of Macro names
 * Through this call, user has access to all macros in Filerx.
 */
void SciTEBase::AskMacroList() {
	if (extender)
		extender->OnMacro("macro:getlist", "");
}

/**
 * List of Macro names has been created. Ask Scintilla to show it.
 */
bool SciTEBase::StartMacroList(const char *words) {
	if (words) {
		wEditor.UserListShow(2, words); //listtype=2
	}

	return true;
}

/**
 * User has chosen a macro in the list. Ask director to execute it.
 */
void SciTEBase::ContinueMacroList(const char *stext) {
	if ((extender) && (*stext != '\0')) {
		currentMacro = stext;
		StartPlayMacro();
	}
}

/**
 * Menu/Toolbar command "Play current macro" (or called from ContinueMacroList).
 */
void SciTEBase::StartPlayMacro() {
	if (extender)
		extender->OnMacro("macro:run", currentMacro.c_str());
}

/*
SciTE received a macro command from director : execute it.
If command needs answer (SCI_GETTEXTLENGTH ...) : give answer to director
*/

namespace {

uintptr_t ReadNum(const char *&t) noexcept {
	assert(t);
	const char *argend = strchr(t, ';');	// find ';'
	uintptr_t v = 0;
	if (*t)
		v = IntegerFromText(t);					// read value
	t = (argend) ? (argend + 1) : nullptr;	// update pointer
	return v;						// return value
}

}

void SciTEBase::ExecuteMacroCommand(const char *command) {
	const char *nextarg = command;
	uintptr_t wParam = 0;
	intptr_t lParam = 0;
	intptr_t rep = 0;				//Scintilla's answer
	const char *answercmd = nullptr;
	SA::Position l = 0;
	std::string string1;	// Long scope as address taken
	char params[4] = "";
	// This code does not validate its input which may cause crashes when bad.
	// 'params' describes types of return values and of arguments.
	// There are exactly 3 characters: return type, wParam, lParam.
	// 0 : void or no param
	// I : integer
	// S : string
	// R : string (for wParam only)
	// For example, "4004;0RS;fruit;mango" performs SCI_SETPROPERTY("fruit","mango") with no return

	// Extract message, parameter specification, wParam, lParam

	const SA::Message message = static_cast<SA::Message>(ReadNum(nextarg));
	if (!nextarg) {
		Trace("Malformed macro command.\n");
		return;
	}
	strncpy(params, nextarg, 3);
	params[3] = '\0';
	nextarg += 4;
	if (*(params + 1) == 'R') {
		// in one function wParam is a string  : void SetProperty(string key,string name)
		const char *s1 = nextarg;
		while (*nextarg != ';')
			nextarg++;
		string1.assign(s1, nextarg - s1);
		wParam = UptrFromString(string1.c_str());
		nextarg++;
	} else {
		wParam = ReadNum(nextarg);
	}

	if (*(params + 2) == 'S')
		lParam = SptrFromString(nextarg);
	else if ((*(params + 2) == 'I') && nextarg)	// nextarg check avoids warning from clang analyze
		lParam = IntegerFromText(nextarg);

	if (*params == '0') {
		// no answer ...
		wEditor.Call(message, wParam, lParam);
		return;
	}

	if (*params == 'S') {
		// string answer
		if (message == SA::Message::GetSelText) {
			l = wEditor.GetSelText(nullptr);
			wParam = 0;
		} else if (message == SA::Message::GetCurLine) {
			const SA::Line line = wEditor.LineFromPosition(wEditor.CurrentPos());
			l = wEditor.LineLength(line);
			wParam = l;
		} else if (message == SA::Message::GetText) {
			l = wEditor.Length();
			wParam = l;
		} else if (message == SA::Message::GetLine) {
			l = wEditor.LineLength(wParam);
		} else {
			l = 0; //unsupported calls EM
		}
		answercmd = "stringinfo:";

	} else {
		//int answer
		answercmd = "intinfo:";
		l = 30;
	}

	std::string tbuff = answercmd;
	const size_t alen = strlen(answercmd);
	tbuff.resize(l + alen + 1);
	if (*params == 'S')
		lParam = SptrFromPointer(&tbuff[alen]);

	if (l > 0)
		rep = wEditor.Call(message, wParam, lParam);
	if (*params == 'I') {
		const std::string sRep = std::to_string(rep);
		tbuff = answercmd;
		tbuff += sRep;
	}
	extender->OnMacro("macro", tbuff.c_str());
}

/**
 * Process all the command line arguments.
 * Arguments that start with '-' (also '/' on Windows) are switches or commands with
 * other arguments being file names which are opened. Commands are distinguished
 * from switches by containing a ':' after the command name.
 * The print switch /p is special cased.
 * Processing occurs in two phases to allow switches that occur before any file opens
 * to be evaluated before creating the UI.
 * Call twice, first with phase=0, then with phase=1 after creating UI.
 */

bool SciTEBase::ProcessCommandLine(const std::vector<GUI::gui_string> &args, int phase) {
	bool performPrint = false;
	bool evaluate = phase == 0;
	for (size_t i = 0; i < args.size(); i++) {
		GUI::gui_string_view arg = args[i];
		if (!arg.empty() && IsSwitchCharacter(arg[0])) {
			arg.remove_prefix(1);
			if (arg.empty() || arg == GUI_TEXT("-")) {
				if (phase == 1) {
					OpenFromStdin(arg[0] == '-');
				}
			} else if (arg.starts_with(GUI_TEXT("@"))) {
				if (phase == 1) {
					OpenFilesFromStdin();
				}
			} else if (arg == GUI_TEXT("p") || arg == GUI_TEXT("P")) {
				performPrint = true;
			} else if (arg == GUI_TEXT("grep") && (args.size() - i >= 5) && (args[i+1].size() >= 4)) {
				// in form -grep [w~][c~][d~][b~] "<file-patterns>" "<excluded-patterns>" "<search-string>"
				GrepFlags gf = GrepFlags::stdOut;
				if (args[i+1][0] == 'w')
					gf = gf | GrepFlags::wholeWord;
				if (args[i+1][1] == 'c')
					gf = gf | GrepFlags::matchCase;
				if (args[i+1][2] == 'd')
					gf = gf | GrepFlags::dot;
				if (args[i+1][3] == 'b')
					gf = gf | GrepFlags::binary;
				std::string sSearch = GUI::UTF8FromString(args[i+4]);
				std::string unquoted = UnSlashString(sSearch);
				SA::Position originalEnd = 0;
				InternalGrep(gf, FilePath::GetWorkingDirectory(), args[i+2], args[i+3], unquoted, originalEnd);
				exit(0);
			} else {
				if (AfterName(arg) == ':') {
					if (arg.starts_with(GUI_TEXT("open:")) || arg.starts_with(GUI_TEXT("loadsession:"))) {
						if (phase == 0)
							return performPrint;
						else
							evaluate = true;
					}
					if (evaluate) {
						const std::string sArg = GUI::UTF8FromString(arg);
						PerformOne(sArg);
					}
				} else {
					if (evaluate) {
						props.ReadLine(GUI::UTF8FromString(arg), PropSetFile::ReadLineState::active,
							       FilePath::GetWorkingDirectory(), filter, nullptr, 0);
					}
				}
			}
		} else {	// Not a switch: it is a file name
			if (phase == 0)
				return performPrint;
			else
				evaluate = true;

			if (!buffers.initialised) {
				InitialiseBuffers();
				if (props.GetInt("save.recent"))
					RestoreRecentMenu();
				if (props.GetInt("load.session.always") && props.GetInt("buffers") && props.GetInt("save.session") && props.GetInt("check.if.already.open"))
					RestoreSession();
			}

			if (!PreOpenCheck(args[i]))
				Open(args[i], static_cast<OpenFlags>(ofQuiet|ofSynchronous));
		}
	}
	if (phase == 1) {
		// If we have finished with all args and no buffer is open
		// try to load session.
		if (!buffers.initialised) {
			InitialiseBuffers();
			if (props.GetInt("save.recent"))
				RestoreRecentMenu();
			if (props.GetInt("buffers") && props.GetInt("save.session"))
				RestoreSession();
		}
		// No open file after session load so create empty document.
		if (filePath.IsUntitled() && buffers.length == 1 && !buffers.buffers[0].isDirty) {
			Open(FilePath());
		}
	}
	return performPrint;
}

// Implement ExtensionAPI methods
intptr_t SciTEBase::Send(Pane p, SA::Message msg, uintptr_t wParam, intptr_t lParam) {
	if (p == paneEditor)
		return lEditor->Call(msg, wParam, lParam);
	else
		return wOutput.Call(msg, wParam, lParam);
}
std::string SciTEBase::Range(Pane p, SA::Span range) {
	if (p == paneEditor)
		return lEditor->StringOfRange(range);
	else
		return wOutput.StringOfRange(range);
}
void SciTEBase::Remove(Pane p, SA::Position start, SA::Position end) {
	if (p == paneEditor) {
		lEditor->DeleteRange(start, end-start);
	} else {
		wOutput.DeleteRange(start, end-start);
	}
}

void SciTEBase::Insert(Pane p, SA::Position pos, const char *s) {
	if (p == paneEditor)
		lEditor->InsertText(pos, s);
	else
		wOutput.InsertText(pos, s);
}

void SciTEBase::Trace(const char *s) {
	ShowOutputOnMainThread();
	OutputAppendStringSynchronised(s);
}

std::string SciTEBase::Property(const char *key) {
	return props.GetExpandedString(key);
}

void SciTEBase::SetProperty(const char *key, const char *val) {
	const std::string value = props.GetExpandedString(key);
	if (value != val) {
		props.Set(key, val);
		needReadProperties = true;
	}
}

void SciTEBase::UnsetProperty(const char *key) {
	props.Unset(key);
	needReadProperties = true;
}

uintptr_t SciTEBase::GetInstance() {
	return 0;
}

void SciTEBase::ShutDown() {
	QuitProgram();
}

void SciTEBase::Perform(const char *actionList) {
	std::vector<char> vActions(actionList, actionList + strlen(actionList) + 1);
	char *actions = vActions.data();
	char *nextAct;
	while ((nextAct = strchr(actions, '\n')) != nullptr) {
		*nextAct = '\0';
		PerformOne(actions);
		actions = nextAct + 1;
	}
	PerformOne(actions);
}

void SciTEBase::DoMenuCommand(int cmdID) {
	MenuCommand(cmdID, 0);
}

SA::ScintillaCall &SciTEBase::PaneCaller(Pane p) noexcept {
	if (p == paneEditor)
		return *lEditor;
	else
		return wOutput;
}

void SciTEBase::SetFindInFilesOptions() {
	const std::string wholeWordName = std::string("find.option.wholeword.") + StdStringFromInteger(wholeWord);
	props.Set("find.wholeword", props.GetNewExpandString(wholeWordName));
	const std::string matchCaseName = std::string("find.option.matchcase.") + StdStringFromInteger(matchCase);
	props.Set("find.matchcase", props.GetNewExpandString(matchCaseName));
}
