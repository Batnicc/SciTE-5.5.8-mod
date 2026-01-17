// Scintilla source code edit control
// @file LexAhk.cxx
// Lexer for ahk3 https://www.ahkscript.com/site/
// by Jos van der Zande, jvdzande@yahoo.com
//
// Changes:
// March 28, 2004 - Added the standard Folding code
// April 21, 2004 - Added Preprosessor Table + Syntax Highlighting
//                  Fixed Number highlighting
//                  Changed default isoperator to IsAOperator to have a better match to ahk3
//                  Fixed "#comments_start" -> "#comments-start"
//                  Fixed "#comments_end" -> "#comments-end"
//                  Fixed Sendkeys in Strings when not terminated with }
//                  Added support for Sendkey strings that have second parameter e.g. {UP 5} or {a down}
// April 26, 2004 - Fixed # pre-processor statement inside of comment block would invalidly change the color.
//                  Added logic for #include <xyz.Ahk> to treat the <> as string
//                  Added underscore to IsAOperator.
// May 17, 2004   - Changed the folding logic from indent to keyword folding.
//                  Added Folding logic for blocks of single-commentlines or commentblock.
//                        triggered by: fold.comment=1
//                  Added Folding logic for preprocessor blocks triggered by fold.preprocessor=1
//                  Added Special for #region - #endregion syntax highlight and folding.
// May 30, 2004   - Fixed issue with continuation lines on If statements.
// June 5, 2004   - Added comma to Operators for better readability.
//                  Added fold.compact support set with fold.compact=1
//                  Changed folding inside of /*-*/. Default is no keyword folding inside comment blocks when fold.comment=1
//                        it will now only happen when fold.comment=2.
// Sep 5, 2004    - Added logic to handle colourizing words on the last line.
//                        Typed Characters now show as "default" till they match any table.
// Oct 10, 2004   - Added logic to show Comments in "Special" directives.
// Nov  1, 2004   - Added better testing for Numbers supporting x and e notation.
// Nov 28, 2004   - Added logic to handle continuation lines for syntax highlighting.
// Jan 10, 2005   - Added Abbreviations Keyword used for expansion
// Mar 24, 2005   - Updated Abbreviations Keywords to fix when followed by Operator.
// Apr 18, 2005   - Updated *//#Comment-End logic to take a linecomment ";" into account
//                - Added folding support for With...EndWith
//                - Added support for a DOT in variable names
//                - Fixed Underscore in CommentBlock
// May 23, 2005   - Fixed the SentKey lexing in case of a missing }
// Aug 11, 2005   - Fixed possible bug with FullWord length > 100.
// Aug 23, 2005   - Added Switch/endswitch support to the folding logic.
// Sep 27, 2005   - Fixed the SentKey lexing logic in case of multiple sentkeys.
// Mar 12, 2006   - Fixed issue with <> coloring as String in stead of Operator in rare occasions.
// Apr  8, 2006   - Added support for ahk3 Standard UDF library (SCE_AHK_UDF)
// Mar  9, 2007   - Fixed bug with + following a String getting the wrong Color.
// Jun 20, 2007   - Fixed Commentblock issue when LF's are used as EOL.
// Jul 26, 2007   - Fixed #endregion undetected bug.
//
// Copyright for Scintilla: 1998-2001 by Neil Hodgson <neilh@scintilla.org>
// The License.txt file describes the conditions under which this software may be distributed.
// Scintilla source code edit control

#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <stdarg.h>
#include <assert.h>
#include <ctype.h>

#include <string>
#include <string_view>

#include "ILexer.h"
#include "Scintilla.h"
#include "SciLexer.h"

#include "WordList.h"
#include "LexAccessor.h"
#include "Accessor.h"
#include "StyleContext.h"
#include "CharacterSet.h"
#include "LexerModule.h"

using namespace Lexilla;

static inline bool IsTypeCharacter(const int ch)
{
	return ch == '$';
}
static inline bool IsAWordChar(const int ch)
{
	return (ch > 0x00) && (ch < 0x80) && (isalnum(ch) || ch == '_');
}

static inline bool IsAWordStart(const int ch)
{
	return (ch > 0x00) && (ch < 0x80) && (isalnum(ch) || ch == '_' || ch == '@' || ch == '#' || ch == '$' || ch == '.');
}

static inline bool IsAOperator(const int ch) {
	if (IsASCII(ch) && isalnum(ch))
		return false;
	if (ch > 0x80)
		return false;
	if (ch == '+' || ch == '-' || ch == '*' || ch == '/' ||
		ch == '&' || ch == '^' || ch == '=' || ch == '<' || ch == '>' ||
		ch == ',' || ch == '%')
		return true;
	return false;
}

///////////////////////////////////////////////////////////////////////////////
// GetSendKey() filters the portion before and after a/multiple space(s)
// and return the first portion to be looked-up in the table
// also check if the second portion is valid... (up,down.on.off,toggle or a number)
///////////////////////////////////////////////////////////////////////////////

static int GetSendKey(const char* szLine, char* szKey)
{
	int		nFlag = 0;
	int		nStartFound = 0;
	int		nKeyPos = 0;
	int		nSpecPos = 0;
	int		nSpecNum = 1;
	int		nPos = 0;
	char	cTemp;
	char	szSpecial[100];

	// split the portion of the sendkey in the part before and after the spaces
	while (((cTemp = szLine[nPos]) != '\0'))
	{
		// skip leading Ctrl/Shift/Alt state
		if (cTemp == '{') {
			nStartFound = 1;
		}
		//
		if (nStartFound == 1) {
			if ((cTemp == ' ') && (nFlag == 0)) // get the stuff till first space
			{
				nFlag = 1;
				// Add } to the end of the first bit for table lookup later.
				szKey[nKeyPos++] = '}';
			}
			else if (cTemp == ' ')
			{
				// skip other spaces
			}
			else if (nFlag == 0)
			{
				// save first portion into var till space or } is hit
				szKey[nKeyPos++] = cTemp;
			}
			else if ((nFlag == 1) && (cTemp != '}'))
			{
				// Save second portion into var...
				szSpecial[nSpecPos++] = cTemp;
				// check if Second portion is all numbers for repeat fuction
				if (isdigit(cTemp) == false) { nSpecNum = 0; }
			}
		}
		nPos++;									// skip to next char

	} // End While


	// Check if the second portion is either a number or one of these keywords
	szKey[nKeyPos] = '\0';
	szSpecial[nSpecPos] = '\0';
	if (strcmp(szSpecial, "down") == 0 || strcmp(szSpecial, "up") == 0 ||
		strcmp(szSpecial, "on") == 0 || strcmp(szSpecial, "off") == 0 ||
		strcmp(szSpecial, "toggle") == 0 || nSpecNum == 1)
	{
		nFlag = 0;
	}
	else
	{
		nFlag = 1;
	}
	return nFlag;  // 1 is bad, 0 is good

} // GetSendKey()

//
// Routine to check the last "none comment" character on a line to see if its a continuation
//
static bool IsContinuationLine(Sci_PositionU szLine, Accessor& styler)
{
	Sci_Position nsPos = styler.LineStart(szLine);
	Sci_Position nePos = styler.LineStart(szLine + 1) - 2;
	//int stylech = styler.StyleAt(nsPos);
	while (nsPos < nePos)
	{
		//stylech = styler.StyleAt(nePos);
		int stylech = styler.StyleAt(nsPos);
		if (!(stylech == SCE_AHK_COMMENT)) {
			char ch = styler.SafeGetCharAt(nePos);
			if (!isspacechar(ch)) {
				if (ch == '_')
					return true;
				else
					return false;
			}
		}
		nePos--; // skip to next char
	} // End While
	return false;
} // IsContinuationLine()

//
// syntax highlighting logic
static void ColouriseAhkDoc(Sci_PositionU startPos,
	Sci_Position length, int initStyle,
	WordList* keywordlists[],
	Accessor& styler) {

	WordList& keywords = *keywordlists[0];
	WordList& keywords2 = *keywordlists[1];
	WordList& keywords3 = *keywordlists[2];
	WordList& keywords4 = *keywordlists[3];
	WordList& keywords5 = *keywordlists[4];
	WordList& keywords6 = *keywordlists[5];
	WordList& keywords7 = *keywordlists[6];
	WordList& keywords8 = *keywordlists[7];
	// find the first previous line without continuation character at the end
	Sci_Position lineCurrent = styler.GetLine(startPos);
	Sci_Position s_startPos = startPos;
	// When not inside a Block comment: find First line without _
	if (initStyle != SCE_AHK_DEFAULT) {
		while ((lineCurrent > 0 && styler.StyleAt(lineCurrent) != SCE_AHK_DEFAULT)) {
			lineCurrent--;
			startPos = styler.LineStart(lineCurrent); // get start position
			initStyle = SCE_AHK_DEFAULT;                           // reset the start style to 0
		}
	}
	// Set the new length to include it from the start and set the start position
	length = length + s_startPos - startPos; // +(startPos - styler.LineStart(lineCurrent + 200));      // correct the total length to process
	styler.StartAt(startPos);
	if (length > styler.Length()) {
		length = styler.Length();
	}

	StyleContext sc(startPos, length, initStyle, styler);
	char si;     // string indicator "=1 '=2
	char ni;     // Numeric indicator error=9 normal=0 normal+dec=1 hex=2 Enot=3
	char ci;     // comment indicator 0=not linecomment(;)
	char ss;	// The escape character `
	char FullWord[100] = ""; // contains word from begining
	si = 0;
	ni = 0;
	ci = 0;
	ss = 0;

	if (initStyle == SCE_AHK_STRING) {
		// Нам нужно "отмотать" назад и посмотреть, какой символ открыл строку
		Sci_Position pos = startPos;
		while (pos > 0 && styler.StyleAt(pos - 1) == SCE_AHK_STRING) {
			pos--;
		}
		char opener = styler.SafeGetCharAt(pos);
		si = (opener == '\"') ? 0 : 1;
	}
	//if (initStyle != SCE_AHK_DEFAULT) {
	//	while (startPos > 0 && styler.StyleAt(styler.LineStart(startPos)) != SCE_AHK_DEFAULT) {
	//		startPos--;
	//	}
	//	// Теперь обновляем startPos на начало найденной "безопасной" строки
	//	startPos = styler.LineStart(startPos-1);
	//	initStyle = (startPos > 0) ? styler.StyleAt(startPos - 1) : SCE_AHK_DEFAULT;
	//}
	//$$$
	for (; sc.More(); sc.Forward()) {
		// current word
		char CurWord[100];
		sc.GetCurrentLowered(CurWord, sizeof(CurWord));
		// **********************************************
		// save the total current word for eof processing
		if (IsAWordChar(sc.ch) || sc.ch == '}')
		{
			strcpy(FullWord, CurWord);
			int tp = static_cast<int>(strlen(FullWord));
			if (tp < 99) {
				FullWord[tp] = static_cast<unsigned char>(tolower(sc.ch));
				FullWord[tp + 1] = '\0';
			}
		}
		// **********************************************
		//
		switch (sc.state)
		{
		case SCE_AHK_COMMENTBLOCK:
		{
			if (ci == 1)
			{
				ci = 0;
				sc.SetState(SCE_AHK_DEFAULT);
				break;
			}
			if ((sc.ch == '/' && sc.chPrev == '*')) {
				ci = 1;
			}
			break;
		}
		case SCE_AHK_COMMENT:
		{
			if (sc.atLineEnd) { sc.SetState(SCE_AHK_DEFAULT); }
			break;
		}
		case SCE_AHK_OPERATOR:
		{
			// check if its a COMobject
			if (sc.chPrev == '.' && IsAWordChar(sc.ch)) {
				sc.SetState(SCE_AHK_COMOBJ);
			}
			else {
				sc.SetState(SCE_AHK_DEFAULT);
			}
			break;
		}
		case SCE_AHK_KEYWORD6:
		{
			if (sc.ch == ';') { sc.SetState(SCE_AHK_COMMENT); }
			if (sc.atLineEnd) { sc.SetState(SCE_AHK_DEFAULT); }
			break;
		}
		case SCE_AHK_KEYWORD:
		{
			if (!(IsAWordChar(sc.ch) || (sc.ch == '-' && (strcmp(CurWord, "#comments") == 0 || strcmp(CurWord, "#include") == 0))))
			{
				if (!IsTypeCharacter(sc.ch))
				{
					//if (strcmp(CurWord, "/*") == 0)
					//{
					//	sc.ChangeState(SCE_AHK_COMMENTBLOCK);
					//	sc.SetState(SCE_AHK_COMMENTBLOCK);
					//	break;
					//}
					//else 
					if (keywords.InList(CurWord)) {
						sc.ChangeState(SCE_AHK_KEYWORD);
						sc.SetState(SCE_AHK_DEFAULT);
					}
					else if (keywords2.InList(CurWord)) {
						sc.ChangeState(SCE_AHK_KEYWORD2);
						sc.SetState(SCE_AHK_DEFAULT);
					}
					else if (keywords3.InList(CurWord)) {
						sc.ChangeState(SCE_AHK_KEYWORD3);
						sc.SetState(SCE_AHK_DEFAULT);
					}
					else if (keywords4.InList(CurWord)) {
						sc.ChangeState(SCE_AHK_KEYWORD4);
						sc.SetState(SCE_AHK_DEFAULT);
					}
					else if (keywords5.InList(CurWord)) {
						sc.ChangeState(SCE_AHK_KEYWORD5);
						sc.SetState(SCE_AHK_DEFAULT);
					}
					else if (keywords6.InList(CurWord)) {
						sc.ChangeState(SCE_AHK_KEYWORD6);
						sc.SetState(SCE_AHK_KEYWORD6);
					}
					else if (keywords7.InList(CurWord) && (!IsAOperator(sc.ch))) {
						sc.ChangeState(SCE_AHK_KEYWORD7);
						sc.SetState(SCE_AHK_DEFAULT);
					}
					else if (keywords8.InList(CurWord)) {
						sc.ChangeState(SCE_AHK_KEYWORD8);
						sc.SetState(SCE_AHK_DEFAULT);
					}
					else if (strcmp(CurWord, "_") == 0) {
						sc.ChangeState(SCE_AHK_OPERATOR);
						sc.SetState(SCE_AHK_DEFAULT);
					}
					else if (!IsAWordChar(sc.ch)) {
						sc.ChangeState(SCE_AHK_DEFAULT);
						sc.SetState(SCE_AHK_DEFAULT);
					}
				}
			}
			if (sc.atLineEnd) {
				sc.SetState(SCE_AHK_DEFAULT);
			}
			break;
		}
		case SCE_AHK_NUMBER:
		{
			// Numeric indicator error=9 normal=0 normal+dec=1 hex=2 E-not=3
			//
			// test for Hex notation
			if (strcmp(CurWord, "0") == 0 && (sc.ch == 'x' || sc.ch == 'X') && ni == 0)
			{
				ni = 2;
				break;
			}
			// test for E notation
			if (IsADigit(sc.chPrev) && (sc.ch == 'e' || sc.ch == 'E') && ni <= 1)
			{
				ni = 3;
				break;
			}
			//  Allow Hex characters inside hex numeric strings
			if ((ni == 2) &&
				(sc.ch == 'a' || sc.ch == 'b' || sc.ch == 'c' || sc.ch == 'd' || sc.ch == 'e' || sc.ch == 'f' ||
					sc.ch == 'A' || sc.ch == 'B' || sc.ch == 'C' || sc.ch == 'D' || sc.ch == 'E' || sc.ch == 'F'))
			{
				break;
			}
			// test for 1 dec point only
			if (sc.ch == '.')
			{
				if (ni == 0)
				{
					ni = 1;
				}
				else
				{
					ni = 9;
				}
				break;
			}
			// end of numeric string ?
			if (!(IsADigit(sc.ch)))
			{
				if (ni == 9)
				{
					sc.ChangeState(SCE_AHK_DEFAULT);
				}
				sc.SetState(SCE_AHK_DEFAULT);
			}
			break;
		}
		case SCE_AHK_VARIABLE:
		{
			// Check if its a COMObject
			if (sc.ch == '.' && !IsADigit(sc.chNext)) {
				sc.SetState(SCE_AHK_OPERATOR);
			}
			else if (!IsAWordChar(sc.ch)) {
				sc.SetState(SCE_AHK_DEFAULT);
			}
			break;
		}
		case SCE_AHK_COMOBJ:
		{
			if (!(IsAWordChar(sc.ch))) {
				if (keywords.InList(CurWord)) {
					sc.ChangeState(SCE_AHK_KEYWORD);
					sc.SetState(SCE_AHK_DEFAULT);
				}
				else { sc.SetState(SCE_AHK_DEFAULT); }
			}
			break;
		}
		//case SCE_AHK_KEYWORD4:
		//{
		//	// Send key string ended
		//	if (sc.chPrev == '}' && sc.ch != '}')
		//	{
		//		// set color to SENDKEY when valid sendkey .. else set back to regular string
		//		char sk[100];
		//		// split {111 222} and return {111} and check if 222 is valid.
		//		// if return code = 1 then invalid 222 so must be string
		//		if (GetSendKey(CurWord, sk))
		//		{
		//			sc.ChangeState(SCE_AHK_STRING);
		//		}
		//		// if single char between {?} then its ok as sendkey for a single character
		//		else if (strlen(sk) == 3)
		//		{
		//			sc.ChangeState(SCE_AHK_KEYWORD4);
		//		}
		//		// if sendkey {111} is in table then ok as sendkey
		//		else if (keywords4.InList(sk))
		//		{
		//			sc.ChangeState(SCE_AHK_KEYWORD4);
		//		}
		//		else
		//		{
		//			sc.ChangeState(SCE_AHK_STRING);
		//		}
		//		sc.SetState(SCE_AHK_STRING);
		//	}
		//	else
		//	{
		//		// check if the start is a valid SendKey start
		//		Sci_Position		nPos = 0;
		//		int		nState = 1;
		//		char	cTemp;
		//		while (!(nState == 2) && ((cTemp = CurWord[nPos]) != '\0'))
		//		{
		//			if (cTemp == '{' && nState == 1)
		//			{
		//				nState = 2;
		//			}
		//			if (nState == 1 && !(cTemp == '+' || cTemp == '!' || cTemp == '^' || cTemp == '#'))
		//			{
		//				nState = 0;
		//			}
		//			nPos++;
		//		}
		//		//Verify characters infront of { ... if not assume  regular string
		//		if (nState == 1 && (!(sc.ch == '{' || sc.ch == '+' || sc.ch == '!' || sc.ch == '^' || sc.ch == '#'))) {
		//			sc.ChangeState(SCE_AHK_STRING);
		//			sc.SetState(SCE_AHK_STRING);
		//		}
		//		// If invalid character found then assume its a regular string
		//		if (nState == 0) {
		//			sc.ChangeState(SCE_AHK_STRING);
		//			sc.SetState(SCE_AHK_STRING);
		//		}
		//	}
		//	// check if next portion is again a sendkey
		//	//if (sc.atLineEnd)
		//	//{
		//	//	sc.ChangeState(SCE_AHK_STRING);
		//	//	sc.SetState(SCE_AHK_DEFAULT);
		//	//	si = 0;  // reset string indicator
		//	//}
		//	//* check in next characters following a sentkey are again a sent key
		//	// Need this test incase of 2 sentkeys like {F1}{ENTER} but not detect {{}
		//	if (sc.state == SCE_AHK_STRING && (sc.ch == '{' || sc.ch == '+' || sc.ch == '!' || sc.ch == '^' || sc.ch == '#')) {
		//		sc.SetState(SCE_AHK_KEYWORD4);
		//	}
		//	// check to see if the string ended...
		//	// Sendkey string isn't complete but the string ended....
		//	if ((si == 0 && sc.ch == '\"') || (si == 1 && sc.ch == '\''))
		//	{
		//		sc.ChangeState(SCE_AHK_STRING);
		//		sc.ForwardSetState(SCE_AHK_DEFAULT);
		//	}
		//	break;
		//}
		case SCE_AHK_STRING:
		{
			// check for " to end a double qouted string or
			// check for ' to end a single qouted string
			if (ss == 1) {
				ss = 0;
				sc.ChangeState(SCE_AHK_ASSIGNMENT);
				sc.SetState(SCE_AHK_STRING);
			}
			if ((si == 0 && sc.ch == '\"') || (si == 1 && sc.ch == '\''))
			{
				sc.ForwardSetState(SCE_AHK_DEFAULT);
				break;
			}
			// find escape char in a string
			if (sc.ch == '`') {
				ss = 1;
				sc.SetState(SCE_AHK_ASSIGNMENT);
			}
			// find Sendkeys in a STRING
			if (sc.ch == '{' || sc.ch == '+' || sc.ch == '!' || sc.ch == '^' || sc.ch == '#') {
//				sc.SetState(SCE_AHK_KEYWORD4);
			}
			break;
		}
		case SCE_AHK_ASSIGNMENT:
		{
			// check if its a ":="
			if (sc.chPrev == ':' && sc.ch == '=') {
				sc.SetState(SCE_AHK_ASSIGNMENT);
			}
			else if (ss == 1) {
				sc.SetState(SCE_AHK_STRING);
			}
			else {
				sc.SetState(SCE_AHK_DEFAULT);
			}
			break;
		}
		case SCE_AHK_FOLD:
		{
//			sc.ChangeState(SCE_AHK_FOLD);
			sc.SetState(SCE_AHK_DEFAULT);
			break;
		}
		}  //switch (sc.state)

		// Determine if a new state should be entered:

		if (sc.state == SCE_AHK_DEFAULT)
		{
			if (sc.ch == ';') { sc.SetState(SCE_AHK_COMMENT); }
			else if (sc.ch == '/' && sc.chNext == '*') { sc.SetState(SCE_AHK_COMMENTBLOCK); }
			else if (sc.ch == '\"') {
				sc.SetState(SCE_AHK_STRING);
				si = 0;
			}
			else if (sc.ch == '\'') {
				sc.SetState(SCE_AHK_STRING);
				si = 1;
			}
			else if (sc.ch == '{' or sc.ch == '}' or sc.ch == '(' or sc.ch == ')' or sc.ch == '[' or sc.ch == ']') {
				sc.SetState(SCE_AHK_FOLD);
			}
			else if (sc.ch == '#') { sc.SetState(SCE_AHK_KEYWORD); }
			else if (sc.ch == '$') { sc.SetState(SCE_AHK_VARIABLE); }
			else if (sc.ch == '.' && !IsADigit(sc.chNext)) { sc.SetState(SCE_AHK_OPERATOR); }
			else if (sc.ch == '@') { sc.SetState(SCE_AHK_KEYWORD); }
			else if (IsADigit(sc.ch) || (sc.ch == '.' && IsADigit(sc.chPrev)))
			{
				sc.SetState(SCE_AHK_NUMBER);
				ni = 0;
			}
			else if (IsAWordStart(sc.ch)) { sc.SetState(SCE_AHK_KEYWORD); }
			else if (IsAOperator(sc.ch)) { sc.SetState(SCE_AHK_OPERATOR); }
			else if (sc.ch == ':' && sc.chNext == '=') { sc.SetState(SCE_AHK_ASSIGNMENT); }
			else if (sc.atLineEnd) { sc.SetState(SCE_AHK_DEFAULT); }
			ss = 0;
		}
	}      //for (; sc.More(); sc.Forward())

	//*************************************
	// Colourize the last word correctly
	//*************************************
	if (sc.state == SCE_AHK_KEYWORD)
	{
		if (strcmp(FullWord, "/*") == 0)
		{
			sc.ChangeState(SCE_AHK_COMMENTBLOCK);
			sc.SetState(SCE_AHK_COMMENTBLOCK);
		}
		else if (keywords.InList(FullWord)) {
			sc.ChangeState(SCE_AHK_KEYWORD);
			sc.SetState(SCE_AHK_KEYWORD);
		}
		else if (keywords2.InList(FullWord)) {
			sc.ChangeState(SCE_AHK_KEYWORD2);
			sc.SetState(SCE_AHK_KEYWORD2);
		}
		else if (keywords3.InList(FullWord)) {
			sc.ChangeState(SCE_AHK_KEYWORD3);
			sc.SetState(SCE_AHK_KEYWORD3);
		}
		else if (keywords5.InList(FullWord)) {
			sc.ChangeState(SCE_AHK_KEYWORD5);
			sc.SetState(SCE_AHK_KEYWORD5);
		}
		else if (keywords6.InList(FullWord)) {
			sc.ChangeState(SCE_AHK_KEYWORD6);
			sc.SetState(SCE_AHK_KEYWORD6);
		}
		else if (keywords7.InList(FullWord) && sc.atLineEnd) {
			sc.ChangeState(SCE_AHK_KEYWORD7);
			sc.SetState(SCE_AHK_KEYWORD7);
		}
		else if (keywords8.InList(FullWord)) {
			sc.ChangeState(SCE_AHK_KEYWORD8);
			sc.SetState(SCE_AHK_KEYWORD8);
		}
		else {
			sc.ChangeState(SCE_AHK_DEFAULT);
			sc.SetState(SCE_AHK_DEFAULT);
		}
	}
	if (sc.state == SCE_AHK_KEYWORD4)
	{
		// Send key string ended
		if (sc.chPrev == '}' && sc.ch != '}')
		{
			// set color to SENDKEY when valid sendkey .. else set back to regular string
			char sk[100];
			// split {111 222} and return {111} and check if 222 is valid.
			// if return code = 1 then invalid 222 so must be string
			if (GetSendKey(FullWord, sk))
			{
				sc.ChangeState(SCE_AHK_STRING);
			}
			// if single char between {?} then its ok as sendkey for a single character
			else if (strlen(sk) == 3)
			{
				sc.ChangeState(SCE_AHK_KEYWORD4);
			}
			// if sendkey {111} is in table then ok as sendkey
			else if (keywords4.InList(sk))
			{
				sc.ChangeState(SCE_AHK_KEYWORD4);
			}
			else
			{
				sc.ChangeState(SCE_AHK_STRING);
			}
			sc.SetState(SCE_AHK_STRING);
		}
		// check if next portion is again a sendkey
		//if (sc.atLineEnd)
		//{
		//	sc.ChangeState(SCE_AHK_STRING);
		//	sc.SetState(SCE_AHK_DEFAULT);
		//}
	}
	//*************************************
	sc.Complete();
}

//
static bool IsStreamCommentStyle(int style) {
	return style == SCE_AHK_COMMENT || style == SCE_AHK_COMMENTBLOCK;
}

//
// Routine to find first none space on the current line and return its Style
// needed for comment lines not starting on pos 1
static int GetStyleFirstWord(Sci_PositionU szLine, Accessor& styler)
{
	Sci_Position nsPos = styler.LineStart(szLine);
	Sci_Position nePos = styler.LineStart(szLine + 1) - 1;
	while (isspacechar(styler.SafeGetCharAt(nsPos)) && nsPos < nePos)
	{
		nsPos++; // skip to next char

	} // End While
	return styler.StyleAt(nsPos);

} // GetStyleFirstWord()

// Folding
static void FoldAhkDoc(Sci_PositionU startPos, Sci_Position length, int, WordList* [], Accessor& styler) {
	Sci_PositionU endPos = startPos + length;
	Sci_Position currentLine = styler.GetLine(startPos);
	int levelPrev = styler.LevelAt(currentLine) & SC_FOLDLEVELNUMBERMASK;
	int levelCurrent = levelPrev;

	char chPrev = 0;
	for (Sci_PositionU i = startPos; i < endPos; i++) {
		char ch = styler.SafeGetCharAt(i);
		int style = styler.StyleAt(i);

		// Пример: сворачивание по фигурным скобкам, игнорируя их в комментариях/строках
		if (style == SCE_AHK_FOLD) {
			if (ch == '{' or ch == '(' or ch == '[') levelCurrent++;
			if (ch == '}' or ch == ')' or ch == ']') levelCurrent--;
		}
		if (style == SCE_AHK_COMMENTBLOCK) {
			if (ch == '*' and chPrev == '/') levelCurrent++;
			if (ch == '/' and chPrev == '*') levelCurrent--;
		}

		// Если дошли до конца строки или документа
		if (ch == '\n' || i == endPos - 1) {
			int lev = levelPrev;
			if (levelCurrent > levelPrev)
				lev |= SC_FOLDLEVELHEADERFLAG; // Показываем "+" у строки

			if (lev != styler.LevelAt(currentLine)) {
				styler.SetLevel(currentLine, lev);
			}

			currentLine++;
			levelPrev = levelCurrent;
		}
		chPrev = ch;
	}
}
//

static const char* const AhkWordLists[] = {
	"#ahk keywords",
	"#ahk functions",
	"#ahk macros",
	"#ahk Sent keys",
	"#ahk Pre-processors",
	"#ahk Special",
	"#ahk Expand",
	"#ahk UDF",
	0
};
extern const LexerModule lmAhk(SCLEX_AHK, ColouriseAhkDoc, "ahk", FoldAhkDoc, AhkWordLists);
