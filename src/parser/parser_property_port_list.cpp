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

struct PropertyPortScan {
  Parser* parser = nullptr;
  int depth = 1;
  bool expect_formal_name = true;
  bool saw_local = false;
  bool local_run = false;
  bool property_run = false;
  bool clock_default_allowed = true;
  TokenKind prev_kind = TokenKind::kComma;
  TokenKind carry_type_kw = TokenKind::kEof;
  DataType* carry_type = nullptr;
  PortItemShape shape{"property"};

  void HarvestFormalName(Lexer& lexer, ModuleItem* item) {
    if (!shape.typed &&
        ParserPropertySpecHelpers::StartsNamedFormalType(*parser)) {
      BeginDataTypedItem();
      carry_type = ParserPropertySpecHelpers::ParseNamedFormalType(*parser);
      carry_type_kw = TokenKind::kEof;
    }
    auto name_tok = lexer.Next();
    item->prop_formals.push_back(name_tok.text);
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

  void BeginDataTypedItem() {
    if (prev_kind != TokenKind::kKwLocal && prev_kind != TokenKind::kKwInput) {
      local_run = false;
    }
    property_run = false;
    clock_default_allowed = false;
  }

  void HandleBuiltinTypeKw(Lexer& lexer, DiagEngine& diag) {
    BeginDataTypedItem();
    TokenKind kind = lexer.Peek().kind;
    ReportChandleFormal(diag, lexer.Peek());
    carry_type = ParserPropertySpecHelpers::ParseFormalType(*parser);
    carry_type_kw =
        carry_type->packed_dim_left != nullptr ? TokenKind::kEof : kind;
    shape.typed = true;
  }

  void HandlePropertyTypeKw(Lexer& lexer) {
    property_run = true;
    local_run = false;
    saw_local = false;
    clock_default_allowed = false;
    carry_type_kw = lexer.Next().kind;
    carry_type = nullptr;
    shape.typed = true;
  }

  void HandleNonPropertyTypeKw(Lexer& lexer) {
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

  void HandleIllegalDirection(Lexer& lexer, DiagEngine& diag) {
    diag.Error(lexer.Peek().loc, "property port direction must be 'input'",
               Subclause("16.12.19"));
    lexer.Next();
    saw_local = false;
  }

  void HandleInputDirection(Lexer& lexer, DiagEngine& diag) {
    if (!saw_local) {
      diag.Error(lexer.Peek().loc,
                 "property port direction 'input' requires 'local'",
                 Subclause("16.12.19"));
    }
    lexer.Next();
    saw_local = false;
  }

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

void ParsePropertyPortList(Parser& parser, Lexer& lexer, DiagEngine& diag,
                           ModuleItem* item) {
  PropertyPortScan scan;
  scan.parser = &parser;
  while (scan.depth > 0 && !lexer.Peek().Is(TokenKind::kEof)) {
    if (!scan.Step(lexer, diag, item)) break;
  }
}

}  // namespace delta
