#pragma once

#include <string_view>
#include <unordered_set>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "lexer/lexer.h"
#include "lexer/token.h"
#include "parser/ast_module.h"

namespace delta {

class Parser;

bool IsBuiltinTypeKwForLocalVar(TokenKind k);

// A.2.10's property_port_item and sequence_port_item as the port list scans
// read them: `{ attribute_instance }`, the qualifiers and the type each scan
// reads itself, then one formal_port_identifier, `{ variable_dimension }` and
// `[ = actual ]`. `port` names the kind of port, "property" or "sequence", for
// the reports. Tracks the item the scan stands in: whether one has begun,
// which tells an empty list from an item with nothing in it; whether it has
// named its formal; and, between the formal and its default, where only
// variable dimensions stand, the depth of their brackets. Defined in
// src/parser/parser_property_port_list.cpp.
struct PortItemShape {
  const char* port;
  bool open = false;
  bool named = false;
  bool in_tail = false;
  int dim_depth = 0;
  SourceLoc start;

  // At a token of the list's own depth: the item it opens, where none is.
  void Begin(const Token& tok);
  // The item's formal, just read.
  void NameFormal();
  // The `=` opening the formal's default.
  void BeginDefault();
  // An attribute instance at the cursor, read past; answers whether one was.
  bool SkipAttributes(Lexer& lexer);
  // Between the formal and its default: a variable dimension's tokens are
  // read past, and any other token before the `,`, `=` or `)` ending that
  // part is reported under A.2.10 and skipped. Answers whether the token was
  // taken.
  bool SkipTailToken(Lexer& lexer, DiagEngine& diag);
  // At the `,` or `)` ending the item: reports, under A.2.10, an item that
  // began and named no formal, and leaves no item begun.
  void End(DiagEngine& diag);
};

// §16.12's property_port_list, its opening `(` read: records each formal of
// the property declaration `item` through the `)` closing the list. Defined
// in src/parser/parser_property_port_list.cpp.
void ParsePropertyPortList(Parser& parser, Lexer& lexer, DiagEngine& diag,
                           ModuleItem* item);

// §16.10 Syntax 16-13 with §6.18: whether the lexer stands at an
// assertion_variable_declaration, its var_data_type opening with `var`
// (A.2.2.1), with a type keyword a local may be declared with, with a name
// among `known_types` that a variable's name or a packed dimension follows, or
// with a type name written through a package or class scope that a variable's
// name follows, past its packed dimensions; a type name opening a cast,
// `nib_t'(a)`, starts no declaration. The lexer is left where it stood.
bool AtAssertionVariableDecl(
    Lexer& lexer, const std::unordered_set<std::string_view>& known_types);

// A.2.2.1: with the lexer just past a var_data_type's `var`, whether a
// data_type follows, a type keyword a local may be declared with or a type
// name a variable's name follows, rather than the implicit type §6.8 makes
// logic. The lexer is left where it stood.
bool VarWritesDataType(Lexer& lexer);
bool IsDisallowedLocalVarTypeKw(TokenKind k);
bool LexerCheck(Lexer& lexer, TokenKind kind);

// §16.8 with §16.6: reports a sequence's or a property's formal whose type
// keyword, `type_tok`, is chandle, a type no assertion expression may
// reference; reports nothing for any other keyword.
void ReportChandleFormal(DiagEngine& diag, const Token& type_tok);

// §16.10: whether `name` is a local variable of the sequence or property
// declaration `item`, one its body declares or a local variable formal
// argument of its port list (§16.8.2).
bool IsLocalVariableOfDecl(const ModuleItem* item, std::string_view name);

// §16.10 and Annex F.5.1: consumes the parenthesized event group after a
// clocking event's `@` and reports each identifier in it that names a local
// variable of `item`, since a clock's condition may not depend on one. Leaves
// the lexer after the group's closing parenthesis, or where it stood when no
// group opened.
void ScanClockEventGroupForLocals(Lexer& lexer, DiagEngine& diag,
                                  const ModuleItem* item);

// §16.14.7: consumes the system function opening a formal's default value in
// a sequence's or a property's port list, records an inferred clocking or
// disable function on the formal just harvested, and reports one placed
// where §16.14.7 forbids it; `clock_default_allowed` says whether the formal's
// type, written or carried, is untyped or `event`.
void ScanSystemDefaultValue(Lexer& lexer, DiagEngine& diag, ModuleItem* item,
                            bool clock_default_allowed);

}  // namespace delta
