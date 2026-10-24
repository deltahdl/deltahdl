// IEEE 1800-2023 §16.12's property_port_list as a property declaration's
// parse reads it, a scan of the list's tokens that records each formal with
// its type, qualifiers and default, and the shape A.2.10 gives a
// property_port_item or a sequence_port_item, which the sequence port list's
// scan in src/parser/parser_sequence_local_var.cpp shares.
//
// These are their own translation unit rather than part of
// src/parser/parser_sequence_property_decl.cpp, which reached the limit
// assert-no-oversized-source-files enforces when the port list began
// reading attribute instances and holding each item to its production.

#include <format>

#include "common/diagnostic.h"
#include "lexer/lexer.h"
#include "lexer/token.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "parser/parser.h"
#include "parser/parser_property_spec_internal.h"
#include "parser/parser_sequence_property_decl_internal.h"

namespace delta {

void PortItemShape::Begin(const Token& tok) {
  if (open) return;
  open = true;
  start = tok.loc;
}

void PortItemShape::NameFormal() {
  named = true;
  in_tail = true;
}

void PortItemShape::BeginDefault() { in_tail = false; }

bool PortItemShape::SkipAttributes(Lexer& lexer) {
  if (!LexerCheck(lexer, TokenKind::kAttrStart)) return false;
  while (!LexerCheck(lexer, TokenKind::kAttrEnd) &&
         !lexer.Peek().Is(TokenKind::kEof)) {
    lexer.Next();
  }
  lexer.Next();
  return true;
}

bool PortItemShape::SkipTailToken(Lexer& lexer, DiagEngine& diag) {
  if (!in_tail) return false;
  if (LexerCheck(lexer, TokenKind::kLBracket)) {
    ++dim_depth;
    lexer.Next();
    return true;
  }
  if (dim_depth > 0) {
    if (LexerCheck(lexer, TokenKind::kRBracket)) --dim_depth;
    lexer.Next();
    return true;
  }
  if (LexerCheck(lexer, TokenKind::kComma) ||
      LexerCheck(lexer, TokenKind::kEq) ||
      LexerCheck(lexer, TokenKind::kRParen)) {
    return false;
  }
  diag.Error(lexer.Peek().loc,
             std::format("a {} port item takes only variable dimensions and "
                         "a default after its formal",
                         port),
             Subclause("A.2.10"));
  lexer.Next();
  return true;
}

void PortItemShape::End(DiagEngine& diag) {
  if (open && !named) {
    diag.Error(
        start,
        std::format("a {} port item names a formal_port_identifier", port),
        Subclause("A.2.10"));
  }
  open = false;
  typed = false;
  named = false;
  in_tail = false;
  dim_depth = 0;
}

// §16.12 named-property port-list scan state carried across loop iterations.
struct PropertyPortScan {
  // The parser whose lexer the scan reads, which parses a formal's default.
  Parser* parser = nullptr;
  int depth = 1;
  bool expect_formal_name = true;
  bool saw_local = false;
  // §16.12.19 / §16.12.17 Restriction 4: track whether the current formal was
  // declared as a local variable formal argument. `local` qualifies the whole
  // comma-separated run of names until a fresh type specifier (not directly
  // following `local`/`input`) begins a new, unqualified item.
  bool local_run = false;
  // §16.12.18: whether the current formal item was introduced with the type
  // keyword `property`. Like `local`, the property_formal_type qualifies the
  // whole comma-separated run of names until a fresh, differently typed item
  // begins.
  bool property_run = false;
  // §16.14.7: whether the current formal run admits a $inferred_clock default.
  // $inferred_clock may only default a formal that is untyped or of type
  // `event`. A run introduced by `event`/`untyped` (or the initial no-type run)
  // permits it; a data type, `sequence`, or `property` formal does not. Follows
  // the same comma-run persistence as the type qualifiers above.
  bool clock_default_allowed = true;
  TokenKind prev_kind = TokenKind::kComma;
  // §16.12.18 by way of §16.8.1: the type keyword in force for the formals
  // that follow, kEof for untyped, cleared by `untyped` and by a type the
  // keyword alone does not name, which a `[` or a type identifier after it
  // shows; `property`, `sequence` and `event` are kept as themselves.
  TokenKind carry_type_kw = TokenKind::kEof;
  // §16.12: the data type in force for the formals that follow, null for none.
  DataType* carry_type = nullptr;
  // A.2.10: the shape of the property_port_item the scan stands in.
  PortItemShape shape{"property"};

  // Handles the formal-name harvest branch (§16.12 formal_port_identifier).
  void HarvestFormalName(Lexer& lexer, ModuleItem* item) {
    if (!shape.typed &&
        ParserPropertySpecHelpers::StartsNamedFormalType(*parser)) {
      BeginDataTypedItem();
      carry_type = ParserPropertySpecHelpers::ParseNamedFormalType(*parser);
      carry_type_kw = TokenKind::kEof;
    }
    auto name_tok = lexer.Next();
    item->prop_formals.push_back(name_tok.text);
    // §16.12 with §16.8: an untyped formal is recorded as `untyped`.
    bool untyped = carry_type_kw == TokenKind::kEof && carry_type == nullptr;
    item->prop_formal_type_kw.push_back(untyped ? TokenKind::kKwUntyped
                                                : carry_type_kw);
    item->prop_formal_types.push_back(carry_type);
    item->prop_formal_unpacked_dims.emplace_back();
    item->prop_formal_is_local.push_back(local_run);
    item->prop_formal_is_property.push_back(property_run);
    item->prop_formal_has_default.push_back(false);
    item->prop_formal_defaults.push_back(nullptr);
    item->prop_formal_inferred.push_back(InferredDefault::kNone);
    expect_formal_name = false;
    saw_local = false;
    shape.NameFormal();
  }

  // A data type, built-in or user-defined, that does not directly follow
  // `local` or `input` starts a fresh formal item whose qualifiers do not
  // include `local`, so the local-variable run ends here.
  void BeginDataTypedItem() {
    if (prev_kind != TokenKind::kKwLocal && prev_kind != TokenKind::kKwInput) {
      local_run = false;
    }
    // §16.12.18: a data-type formal (one of the §16.6 types) is not a
    // `property` formal, so the property run ends where such a type specifier
    // begins.
    property_run = false;
    // §16.14.7: a data-typed formal is neither untyped nor `event`, so it may
    // not be defaulted to $inferred_clock.
    clock_default_allowed = false;
  }

  // depth==1 built-in type keyword: the data type of a fresh formal item.
  void HandleBuiltinTypeKw(Lexer& lexer, DiagEngine& diag) {
    BeginDataTypedItem();
    TokenKind kind = lexer.Peek().kind;
    ReportChandleFormal(diag, lexer.Peek());
    carry_type = ParserPropertySpecHelpers::ParseFormalType(*parser);
    carry_type_kw =
        carry_type->packed_dim_left != nullptr ? TokenKind::kEof : kind;
    shape.typed = true;
  }

  // §16.12.18: the `property` type keyword begins a run of one or more
  // property-typed formal arguments. A property formal is never a local
  // variable formal, so the local run ends here.
  void HandlePropertyTypeKw(Lexer& lexer) {
    property_run = true;
    local_run = false;
    saw_local = false;
    // §16.14.7: a `property`-typed formal is neither untyped nor `event`, so it
    // may not be defaulted to $inferred_clock.
    clock_default_allowed = false;
    carry_type_kw = lexer.Next().kind;
    carry_type = nullptr;
    shape.typed = true;
  }

  // §16.12.18: the `sequence`, `event`, and `untyped` type keywords begin a
  // differently typed formal item, ending any in-progress property (and local)
  // run.
  void HandleNonPropertyTypeKw(Lexer& lexer) {
    // §16.14.7: `event` and `untyped` formals admit a $inferred_clock default;
    // `sequence` (the other keyword routed here) does not.
    TokenKind kw = lexer.Peek().kind;
    clock_default_allowed =
        kw == TokenKind::kKwEvent || kw == TokenKind::kKwUntyped;
    property_run = false;
    local_run = false;
    saw_local = false;
    carry_type_kw = kw == TokenKind::kKwUntyped ? TokenKind::kEof : kw;
    carry_type = nullptr;
    shape.typed = true;
    lexer.Next();
  }

  // §16.12.19: a local variable formal argument of a named property shall have
  // direction `input`; declaring one with direction `inout` or `output` is
  // illegal. The borrowed A.2.10 production property_lvar_port_direction admits
  // only `input`, so `output` and `inout` have no legal role inside a property
  // port, with or without a preceding `local`.
  void HandleIllegalDirection(Lexer& lexer, DiagEngine& diag) {
    diag.Error(lexer.Peek().loc, "property port direction must be 'input'",
               Subclause("16.12.19"));
    lexer.Next();
    saw_local = false;
  }

  // `input` is permitted only after `local`.
  void HandleInputDirection(Lexer& lexer, DiagEngine& diag) {
    if (!saw_local) {
      diag.Error(lexer.Peek().loc,
                 "property port direction 'input' requires 'local'",
                 Subclause("16.12.19"));
    }
    lexer.Next();
    saw_local = false;
  }

  // Handles the depth==1 (top-level) tokens of the property port list. Returns
  // true if the current token was consumed here; false means the caller falls
  // through to the default skip. All branches assume depth==1 already holds.
  // §16.12 with §16.8: `formal = default` gives the formal just harvested a
  // default actual argument, kept beside it for an instance that omits the
  // formal to take.
  void HandleDefaultEq(Lexer& lexer, ModuleItem* item) {
    lexer.Next();
    expect_formal_name = false;
    shape.BeginDefault();
    if (item->prop_formal_defaults.empty()) return;
    item->prop_formal_has_default.back() = true;
    if (parser == nullptr) return;
    item->prop_formal_defaults.back() =
        ParserPropertySpecHelpers::ParseFormalDefault(*parser);
  }

  bool DispatchTopLevel(Lexer& lexer, DiagEngine& diag, ModuleItem* item) {
    if (LexerCheck(lexer, TokenKind::kComma)) {
      shape.End(diag);
      lexer.Next();
      shape.Begin(lexer.Peek());
      expect_formal_name = true;
      saw_local = false;
    } else if (LexerCheck(lexer, TokenKind::kEq)) {
      HandleDefaultEq(lexer, item);
    } else if (LexerCheck(lexer, TokenKind::kKwLocal)) {
      lexer.Next();
      saw_local = true;
      local_run = true;
    } else if (IsBuiltinTypeKwForLocalVar(lexer.Peek().kind)) {
      HandleBuiltinTypeKw(lexer, diag);
    } else if (LexerCheck(lexer, TokenKind::kKwProperty)) {
      HandlePropertyTypeKw(lexer);
    } else if (LexerCheck(lexer, TokenKind::kKwSequence) ||
               LexerCheck(lexer, TokenKind::kKwEvent) ||
               LexerCheck(lexer, TokenKind::kKwUntyped)) {
      HandleNonPropertyTypeKw(lexer);
    } else if (LexerCheck(lexer, TokenKind::kKwOutput) ||
               LexerCheck(lexer, TokenKind::kKwInout)) {
      HandleIllegalDirection(lexer, diag);
    } else if (LexerCheck(lexer, TokenKind::kKwInput)) {
      HandleInputDirection(lexer, diag);
    } else if (prev_kind == TokenKind::kEq &&
               LexerCheck(lexer, TokenKind::kSystemIdentifier)) {
      ScanSystemDefaultValue(lexer, diag, item, clock_default_allowed);
    } else if (expect_formal_name &&
               LexerCheck(lexer, TokenKind::kIdentifier)) {
      HarvestFormalName(lexer, item);
    } else {
      return false;
    }
    return true;
  }

  // Dispatches one token to its handler, updating scan state. Returns false
  // once the matching ')' for the opening '(' has been consumed.
  bool Dispatch(Lexer& lexer, DiagEngine& diag, ModuleItem* item) {
    if (depth == 1 &&
        (shape.SkipAttributes(lexer) || shape.SkipTailToken(lexer, diag))) {
      return true;
    }
    if (LexerCheck(lexer, TokenKind::kLParen)) {
      lexer.Next();
      ++depth;
      return true;
    }
    if (LexerCheck(lexer, TokenKind::kRParen)) {
      if (depth == 1) shape.End(diag);
      lexer.Next();
      --depth;
      return depth != 0;
    }
    if (depth == 1 && DispatchTopLevel(lexer, diag, item)) return true;
    lexer.Next();
    return true;
  }

  // Consumes one token of the port list. Returns false once the matching ')'
  // for the opening '(' has been consumed (list complete).
  bool Step(Lexer& lexer, DiagEngine& diag, ModuleItem* item) {
    TokenKind this_kind = lexer.Peek().kind;
    if (depth == 1 && this_kind != TokenKind::kRParen) {
      shape.Begin(lexer.Peek());
    }
    bool keep_going = Dispatch(lexer, diag, item);
    prev_kind = this_kind;
    return keep_going;
  }
};

// §16.12 named-property port list. On entry the opening '(' has already been
// consumed; this drains the comma-separated formal list through its matching
// ')' , recording formal names and their local-variable qualification while
// policing the §16.12.19 direction rules and holding each item to A.2.10's
// property_port_item (PortItemShape).
void ParsePropertyPortList(Parser& parser, Lexer& lexer, DiagEngine& diag,
                           ModuleItem* item) {
  PropertyPortScan scan;
  scan.parser = &parser;
  while (scan.depth > 0 && !lexer.Peek().Is(TokenKind::kEof)) {
    if (!scan.Step(lexer, diag, item)) break;
  }
}

}  // namespace delta
