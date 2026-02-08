#include "parser/parser.h"

namespace delta {

// --- Enum type parsing ---

DataType Parser::ParseEnumType() {
  DataType dtype;
  dtype.kind = DataTypeKind::kEnum;
  Expect(TokenKind::kKwEnum);

  // Optional base type (e.g. enum logic [7:0] { ... }).
  auto base = ParseDataType();
  if (base.kind != DataTypeKind::kImplicit) {
    dtype.is_signed = base.is_signed;
    dtype.packed_dim_left = base.packed_dim_left;
    dtype.packed_dim_right = base.packed_dim_right;
  }

  Expect(TokenKind::kLBrace);
  do {
    EnumMember member;
    member.name = Expect(TokenKind::kIdentifier).text;
    if (Match(TokenKind::kEq)) {
      member.value = ParseExpr();
    }
    dtype.enum_members.push_back(member);
  } while (Match(TokenKind::kComma));
  Expect(TokenKind::kRBrace);

  return dtype;
}

// --- Typedef parsing ---

ModuleItem* Parser::ParseTypedef() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kTypedef;
  item->loc = CurrentLoc();
  Expect(TokenKind::kKwTypedef);

  if (Check(TokenKind::kKwEnum)) {
    item->typedef_type = ParseEnumType();
  } else {
    item->typedef_type = ParseDataType();
  }

  item->name = Expect(TokenKind::kIdentifier).text;
  known_types_.insert(item->name);
  Expect(TokenKind::kSemicolon);
  return item;
}

// --- Function argument list ---

std::vector<FunctionArg> Parser::ParseFunctionArgs() {
  std::vector<FunctionArg> args;
  Expect(TokenKind::kLParen);
  if (Check(TokenKind::kRParen)) {
    Consume();
    return args;
  }
  do {
    FunctionArg arg;
    if (Check(TokenKind::kKwInput)) {
      arg.direction = Direction::kInput;
      Consume();
    } else if (Check(TokenKind::kKwOutput)) {
      arg.direction = Direction::kOutput;
      Consume();
    } else if (Check(TokenKind::kKwInout)) {
      arg.direction = Direction::kInout;
      Consume();
    } else if (Check(TokenKind::kKwRef)) {
      arg.direction = Direction::kRef;
      Consume();
    }
    arg.data_type = ParseDataType();
    arg.name = Expect(TokenKind::kIdentifier).text;
    args.push_back(arg);
  } while (Match(TokenKind::kComma));
  Expect(TokenKind::kRParen);
  return args;
}

// --- Function declaration ---

ModuleItem* Parser::ParseFunctionDecl() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kFunctionDecl;
  item->loc = CurrentLoc();
  Expect(TokenKind::kKwFunction);

  // Optional lifetime: automatic or static.
  if (Check(TokenKind::kKwAutomatic) || Check(TokenKind::kKwStatic)) {
    Consume();
  }

  // Return type (may be void or a data type).
  if (Check(TokenKind::kKwVoid)) {
    item->return_type.kind = DataTypeKind::kVoid;
    Consume();
  } else {
    item->return_type = ParseDataType();
  }

  item->name = Expect(TokenKind::kIdentifier).text;

  if (Check(TokenKind::kLParen)) {
    item->func_args = ParseFunctionArgs();
  }
  Expect(TokenKind::kSemicolon);

  while (!Check(TokenKind::kKwEndfunction) && !AtEnd()) {
    item->func_body_stmts.push_back(ParseStmt());
  }
  Expect(TokenKind::kKwEndfunction);
  return item;
}

// --- Task declaration ---

ModuleItem* Parser::ParseTaskDecl() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kTaskDecl;
  item->loc = CurrentLoc();
  Expect(TokenKind::kKwTask);

  if (Check(TokenKind::kKwAutomatic) || Check(TokenKind::kKwStatic)) {
    Consume();
  }

  item->name = Expect(TokenKind::kIdentifier).text;

  if (Check(TokenKind::kLParen)) {
    item->func_args = ParseFunctionArgs();
  }
  Expect(TokenKind::kSemicolon);

  while (!Check(TokenKind::kKwEndtask) && !AtEnd()) {
    item->func_body_stmts.push_back(ParseStmt());
  }
  Expect(TokenKind::kKwEndtask);
  return item;
}

}  // namespace delta
