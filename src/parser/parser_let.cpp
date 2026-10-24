#include "common/arena.h"
#include "common/diagnostic.h"
#include "lexer/token.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "parser/parser.h"
#include "parser/parser_data_decl_internal.h"

namespace delta {

// A.2.12's let_port_item: attribute instances, a let_formal_type, the
// formal's name, its variable dimensions and an optional default. A.2.12
// writes let_formal_type as a data_type_or_implicit or `untyped`, and A.2.2.1
// lets that be a type_reference (§6.23), an inline struct, union or enum, or
// an implicit type of packed dimensions alone. None of them opens with
// `const`, so a `const` there is reported and the type after it read on.
FunctionArg Parser::ParseLetArg() {
  FunctionArg arg;
  ParseAttributes();
  if (Check(TokenKind::kKwConst)) {
    diag_.Error(Consume().loc,
                "a let formal takes no 'const'; its type is a data type, an "
                "implicit type or 'untyped'",
                Subclause("A.2.12"));
  }
  if (Check(TokenKind::kLBracket)) {
    ParsePackedDims(arg.data_type);
  } else if (Match(TokenKind::kKwUntyped)) {
    arg.is_untyped = true;
  } else if (!TryParseInlineAggregateType(arg.data_type) &&
             !ParserDataDeclHelpers::ReadTypeReference(*this, arg.data_type)) {
    arg.data_type = ParseDeclaredDataType();
  }
  arg.name = Expect(TokenKind::kIdentifier, Subclause("11.12")).text;
  ParseUnpackedDims(arg.unpacked_dims);
  if (Match(TokenKind::kEq)) arg.default_value = ParseExpr();
  return arg;
}

ModuleItem* Parser::ParseLetDecl() {
  Consume();
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kLetDecl;
  item->loc = CurrentLoc();
  item->name = ExpectIdentifier(Subclause("11.12")).text;
  if (Check(TokenKind::kLParen)) {
    Consume();
    if (!Check(TokenKind::kRParen)) {
      item->func_args.push_back(ParseLetArg());
      while (Match(TokenKind::kComma)) {
        item->func_args.push_back(ParseLetArg());
      }
    }
    Expect(TokenKind::kRParen, Subclause("11.12"));
  }
  Expect(TokenKind::kEq, Subclause("11.12"));
  item->init_expr = ParseExpr();
  Expect(TokenKind::kSemicolon, Subclause("11.12"));
  return item;
}

}  // namespace delta
