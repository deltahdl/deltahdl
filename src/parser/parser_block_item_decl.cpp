#include <algorithm>
#include <string>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"
#include "parser/parser.h"
#include "parser/parser_data_decl_internal.h"
#include "parser/parser_token_skips.h"

namespace delta {

namespace {

int QualifierRank(TokenKind kind) {
  switch (kind) {
    case TokenKind::kKwConst:
      return 0;
    case TokenKind::kKwVar:
      return 1;
    case TokenKind::kKwStatic:
    case TokenKind::kKwAutomatic:
      return 2;
    default:
      return -1;
  }
}

}  // namespace

DataDeclQualifiers ParserDataDeclHelpers::ReadQualifiers(Parser& p) {
  DataDeclQualifiers quals;
  int last = -1;
  for (int rank = QualifierRank(p.CurrentToken().kind); rank >= 0;
       rank = QualifierRank(p.CurrentToken().kind)) {
    const Token kTok = p.Consume();
    if (rank <= last) {
      p.diag_.Error(kTok.loc,
                    "'" + std::string(kTok.text) +
                        "' is out of place: a data declaration writes "
                        "'const', then 'var', then its lifetime, each at most "
                        "once",
                    Subclause("A.2.1.3"));
    }
    last = std::max(last, rank);
    if (kTok.kind == TokenKind::kKwConst) {
      quals.is_const = true;
    } else if (kTok.kind == TokenKind::kKwVar) {
      quals.has_var = true;
    } else {
      quals.is_automatic = kTok.kind == TokenKind::kKwAutomatic;
      quals.is_static = !quals.is_automatic;
      quals.lifetime_loc = kTok.loc;
    }
  }
  return quals;
}

bool ParserDataDeclHelpers::AtUnitScopedTypeName(Parser& p) {
  if (!p.Check(TokenKind::kSystemIdentifier) ||
      p.CurrentToken().text != "$unit")
    return false;
  auto saved = p.lexer_.SavePos();
  p.Consume();
  bool is_type = p.Match(TokenKind::kColonColon) && p.CheckIdentifier() &&
                 p.known_types_.count(p.CurrentToken().text) != 0;
  p.lexer_.RestorePos(saved);
  return is_type;
}

bool Parser::IsBlockVarDeclStart() {
  auto saved = lexer_.SavePos();
  while (Check(TokenKind::kAttrStart)) {
    Consume();
    int depth = 1;
    while (depth > 0 && !AtEnd()) {
      if (Check(TokenKind::kAttrEnd)) depth--;
      Consume();
    }
  }
  bool result = IsBlockVarDeclStartCore();
  lexer_.RestorePos(saved);
  return result;
}

static bool OpensBlockDeclOutright(TokenKind tk) {
  switch (tk) {
    case TokenKind::kKwAutomatic:
    case TokenKind::kKwStatic:
    case TokenKind::kKwParameter:
    case TokenKind::kKwLocalparam:
    case TokenKind::kKwConst:
    case TokenKind::kKwTypedef:
    case TokenKind::kKwNettype:
    case TokenKind::kKwImport:
    case TokenKind::kKwLet:
    case TokenKind::kKwStruct:
    case TokenKind::kKwUnion:
    case TokenKind::kKwEnum:
    case TokenKind::kKwVar:
    case TokenKind::kKwType:
    case TokenKind::kKwVirtual:
      return true;
    default:
      return false;
  }
}

bool Parser::IsBlockVarDeclStartCore() {
  auto tk = CurrentToken().kind;
  if (OpensBlockDeclOutright(tk)) return true;
  if (IsDataTypeKeyword(tk)) {
    auto saved = lexer_.SavePos();
    Consume();
    bool is_decl = CheckIdentifier() || Check(TokenKind::kKwSigned) ||
                   Check(TokenKind::kKwUnsigned) || Check(TokenKind::kLBracket);
    lexer_.RestorePos(saved);
    return is_decl;
  }
  if (ParserDataDeclHelpers::AtUnitScopedTypeName(*this))
    return !IsScopedCallOrAssignStmt();
  if (!Check(TokenKind::kIdentifier)) return false;
  if (AtCheckerInstantiationStmt()) return false;
  if (known_types_.count(CurrentToken().text) == 0 && !AtScopedTypeName()) {
    return false;
  }
  return !IsScopedCallOrAssignStmt();
}

bool Parser::AtScopedTypeName() {
  auto saved = lexer_.SavePos();
  Consume();
  bool scoped = Match(TokenKind::kColonColon) && CheckIdentifier();
  lexer_.RestorePos(saved);
  return scoped;
}

bool Parser::IsScopedCallOrAssignStmt() {
  auto saved = lexer_.SavePos();
  auto skip_param_values = [this] {
    if (!Check(TokenKind::kHash)) return;
    auto at_hash = lexer_.SavePos();
    Consume();
    if (Check(TokenKind::kLParen)) {
      SkipBalancedParens();
    } else {
      lexer_.RestorePos(at_hash);
    }
  };
  Consume();
  skip_param_values();
  if (Match(TokenKind::kColonColon)) {
    while (CheckIdentifier()) {
      Consume();
      skip_param_values();
      if (!Match(TokenKind::kColonColon)) break;
    }
  }
  SkipBracketedDims();
  bool is_stmt =
      Check(TokenKind::kLParen) || Check(TokenKind::kEq) ||
      Check(TokenKind::kLtEq) || Check(TokenKind::kApostropheLBrace) ||
      Check(TokenKind::kDot) || Check(TokenKind::kPlusPlus) ||
      Check(TokenKind::kMinusMinus) || Check(TokenKind::kSemicolon) ||
      IsCompoundAssignOp(CurrentToken().kind);
  lexer_.RestorePos(saved);
  return is_stmt;
}

void Parser::ParseBlockDataDecl(std::vector<Stmt*>& stmts,
                                const std::vector<Attribute>& attrs) {
  const DataDeclQualifiers kQuals =
      ParserDataDeclHelpers::ReadQualifiers(*this);
  DataType dtype;
  bool is_type_ref = Check(TokenKind::kKwType);
  if (is_type_ref) {
    if (!kQuals.has_var) {
      diag_.Error(CurrentLoc(),
                  "type_reference in a variable declaration must be "
                  "preceded by the 'var' keyword",
                  Subclause("6.8"));
    }
    ParserDataDeclHelpers::ReadTypeReference(*this, dtype);
  } else if (!TryParseInlineAggregateType(dtype)) {
    dtype = ParseDeclaredDataType();
  }
  if (kQuals.has_var && dtype.kind == DataTypeKind::kImplicit &&
      Check(TokenKind::kLBracket)) {
    ParsePackedDims(dtype);
  }

  if (!kQuals.has_var && !is_type_ref &&
      dtype.kind == DataTypeKind::kImplicit) {
    diag_.Error(CurrentLoc(),
                "data_declaration without an explicit data type requires "
                "the 'var' keyword",
                Subclause("6.8"));
  }
  do {
    auto* s = arena_.Create<Stmt>();
    s->kind = StmtKind::kVarDecl;
    s->range.start = CurrentLoc();
    s->var_decl_type = dtype;
    s->var_is_const = kQuals.is_const;
    s->var_is_automatic = kQuals.is_automatic;
    s->var_is_static = kQuals.is_static;
    s->var_name = ExpectIdentifier(Subclause("6.8")).text;
    s->attrs = attrs;
    ParseUnpackedDims(s->var_unpacked_dims);
    if (Match(TokenKind::kEq)) {
      s->var_init = ParseExpr();
    }
    stmts.push_back(s);
  } while (Match(TokenKind::kComma));
  Expect(TokenKind::kSemicolon, Subclause("6.8"));
}

namespace {

Stmt* BlockItemDeclStmt(Arena& arena, ModuleItem* item, SourceLoc loc,
                        std::vector<Attribute> attrs) {
  auto* s = arena.Create<Stmt>();
  s->kind = StmtKind::kBlockItemDecl;
  s->range.start = loc;
  s->decl_item = item;
  s->attrs = std::move(attrs);
  return s;
}

}  // namespace

void Parser::ParseBlockVarDecls(std::vector<Stmt*>& stmts) {
  auto attrs = ParseAttributes();

  if (Check(TokenKind::kKwLet)) {
    SourceLoc loc = CurrentLoc();
    stmts.push_back(
        BlockItemDeclStmt(arena_, ParseLetDecl(), loc, std::move(attrs)));
    return;
  }

  if (Check(TokenKind::kKwTypedef)) {
    SourceLoc loc = CurrentLoc();
    stmts.push_back(
        BlockItemDeclStmt(arena_, ParseTypedef(), loc, std::move(attrs)));
    return;
  }

  if (Check(TokenKind::kKwNettype)) {
    SourceLoc loc = CurrentLoc();
    stmts.push_back(
        BlockItemDeclStmt(arena_, ParseNettypeDecl(), loc, std::move(attrs)));
    return;
  }

  if (Check(TokenKind::kKwImport)) {
    std::vector<ModuleItem*> import_items;
    ParseImportDecl(import_items);
    for (auto* imp : import_items) {
      stmts.push_back(BlockItemDeclStmt(arena_, imp, imp->loc, attrs));
    }
    return;
  }

  if (Check(TokenKind::kKwParameter) || Check(TokenKind::kKwLocalparam)) {
    std::vector<ModuleItem*> param_items;
    ParseParamDecl(param_items);
    for (auto* param : param_items) {
      auto* s = arena_.Create<Stmt>();
      s->kind = StmtKind::kVarDecl;
      s->range.start = param->loc;
      s->var_decl_type = param->data_type;
      s->var_name = param->name;
      s->var_init = param->init_expr;
      s->var_is_param = true;
      s->decl_item = param;
      s->attrs = attrs;
      stmts.push_back(s);
    }
    return;
  }
  ParseBlockDataDecl(stmts, attrs);
}

}  // namespace delta
