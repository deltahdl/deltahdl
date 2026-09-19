// The block item declarations of IEEE 1800-2023 A.2.8, which A.6.3's seq_block
// and par_block and A.2.6's and A.2.7's subroutine bodies open with: the
// predicate that decides whether a block item is a declaration or a statement,
// and the parse of the declaration it admits. These reach the rest of the
// statement parser through Parser::IsBlockVarDeclStart and
// Parser::ParseBlockVarDecls only, both declared in src/parser/parser.h. The
// group moved out of parser_stmt.cpp when the scoped-type predicate took that
// file past the limit assert-no-oversized-source-files enforces.

#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"
#include "parser/parser.h"
#include "parser/parser_token_skips.h"

namespace delta {

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

// The keywords that open a block-item declaration outright, with nothing
// after them to look at: a lifetime, a parameter, `const`, a typedef, an
// import, a let, an aggregate or enum type, `var`, and `virtual` -- A.2.2.1
// lists `virtual [interface] interface_identifier` among data_type's
// alternatives, so a block item opening with it is a §25.9 virtual interface
// declaration wherever A.2.8 places one, the locals of a task or function body
// and the head of a seq_block; no statement opens with the keyword, and
// ParseDataType reads the type from it.
static bool OpensBlockDeclOutright(TokenKind tk) {
  switch (tk) {
    case TokenKind::kKwAutomatic:
    case TokenKind::kKwStatic:
    case TokenKind::kKwParameter:
    case TokenKind::kKwLocalparam:
    case TokenKind::kKwConst:
    case TokenKind::kKwTypedef:
    case TokenKind::kKwImport:
    case TokenKind::kKwLet:
    case TokenKind::kKwStruct:
    case TokenKind::kKwUnion:
    case TokenKind::kKwEnum:
    case TokenKind::kKwVar:
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
  if (!Check(TokenKind::kIdentifier)) return false;
  // A.2.2.1 lets a data_type be a type_identifier behind a package_scope or a
  // class_scope, and A.2.8 admits any data_declaration as a block item, so an
  // identifier followed by `::` opens a declaration whether or not the leading
  // name is one this scope knows as a type: a package name never is, and
  // ParseImplicitTypeOrInst reads the module-level `pkg::t v;` the same way.
  // Only a bare name is held to known_types_; a bare unknown identifier at the
  // head of a block item is a statement, and the undeclared-type reading
  // LooksLikeUndeclaredTypeDecl explains belongs to the module-level path
  // alone, where no statement can stand.
  if (known_types_.count(CurrentToken().text) == 0 && !AtScopedTypeName()) {
    return false;
  }
  // A leading known type name usually begins a declaration (`Type v;`,
  // `pkg::Type v;`), but a scoped call or assignment is a statement, not a
  // declaration (§8.10/§8.23).
  return !IsScopedCallOrAssignStmt();
}

bool Parser::AtScopedTypeName() {
  auto saved = lexer_.SavePos();
  Consume();
  bool scoped = Match(TokenKind::kColonColon) && CheckIdentifier();
  lexer_.RestorePos(saved);
  return scoped;
}

// A.2.2.1's class_type (printed page 1183) lets a parameter_value_assignment
// follow the class identifier before each `::`, and §8.25.1 (printed page 205)
// has a use of the class scope resolution operator outside a parameterized
// class name its specialization, so `C#(bit)::set(1);` is the same statement as
// `C::set(1);` and is told from the declaration `C#(bit) v;` by what follows
// the `#(...)`. The walk below skips the group at each name; before it did,
// the walk stopped at `#`, took the line for a declaration, and ParseNamedType
// met the call's `(` where §6.8 puts a variable name.
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
  Consume();  // the known type name
  skip_param_values();
  if (Match(TokenKind::kColonColon)) {
    while (CheckIdentifier()) {
      Consume();
      skip_param_values();
      if (!Match(TokenKind::kColonColon)) break;
    }
  }
  // A.2.2.1 lets packed dimensions follow the type_identifier, so what decides
  // is the token after any `[...]` groups: `pkg::t [1:0] w;` reaches a variable
  // name there and `pkg::arr[0] = 4;` an assignment operator.
  SkipBracketedDims();
  // A type name reached here either bare or after a `::` scope path. If it is
  // immediately followed by a call `(`, an assignment operator, the `'{` that
  // opens a §10.9 assignment pattern, a `.` member select or a `++`/`--`, it is
  // a statement rather than a declaration: no data_declaration puts any of
  // those after its type's dimensions, and A.2.2.1's one `.` inside a data_type
  // follows `virtual interface`, a keyword and not an identifier. The
  // bare-assignment case covers an embedded covergroup
  // (§19.4): `covergroup cg ... endgroup` implicitly declares both the type
  // `cg` and a variable `cg`, so `cg = new;` is an assignment to that variable,
  // not the start of a `cg <name>` declaration. The `'{` case covers §10.9's
  // assignment_pattern_expression, whose type is written as a prefix before the
  // pattern -- `pair_t'{a, b} = 16'hABCD;` -- so the operator this list is
  // otherwise looking for stands behind the pattern rather than behind the
  // name. It cannot be a declaration: §6.8 continues a data_declaration with a
  // list_of_variable_decl_assignments, which A.2.3 begins with a
  // variable_identifier, so no declaration puts a `'{` after its type.
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
  bool is_const = Match(TokenKind::kKwConst);
  bool is_automatic = Match(TokenKind::kKwAutomatic);
  bool is_static = !is_automatic && Match(TokenKind::kKwStatic);
  bool saw_var = Match(TokenKind::kKwVar);
  if (!is_automatic && !is_static && saw_var) {
    is_automatic = Match(TokenKind::kKwAutomatic);
    is_static = !is_automatic && Match(TokenKind::kKwStatic);
  }
  // ParseDataType reads an identifier as a named type only when known_types_
  // holds it, which a package name never is; the scoped form
  // IsBlockVarDeclStartCore admitted is read here by ParseNamedType, whose
  // `::` walk and `#(...)` parameters are what the leading known-type case
  // reaches through ParseDataType.
  DataType dtype;
  if (Check(TokenKind::kIdentifier) &&
      known_types_.count(CurrentToken().text) == 0 && AtScopedTypeName()) {
    dtype = ParseNamedType();
    ParsePackedDims(dtype);
  } else {
    dtype = ParseDataType();
  }
  if (saw_var && dtype.kind == DataTypeKind::kImplicit &&
      Check(TokenKind::kLBracket)) {
    ParsePackedDims(dtype);
  }

  if (!saw_var && dtype.kind == DataTypeKind::kImplicit) {
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
    s->var_is_const = is_const;
    s->var_is_automatic = is_automatic;
    s->var_is_static = is_static;
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

void Parser::ParseBlockVarDecls(std::vector<Stmt*>& stmts) {
  auto attrs = ParseAttributes();

  if (Check(TokenKind::kKwLet)) {
    auto* s = arena_.Create<Stmt>();
    s->kind = StmtKind::kBlockItemDecl;
    s->range.start = CurrentLoc();
    s->decl_item = ParseLetDecl();
    s->attrs = std::move(attrs);
    stmts.push_back(s);
    return;
  }

  if (Check(TokenKind::kKwTypedef)) {
    auto* s = arena_.Create<Stmt>();
    s->kind = StmtKind::kBlockItemDecl;
    s->range.start = CurrentLoc();
    s->decl_item = ParseTypedef();
    s->attrs = std::move(attrs);
    stmts.push_back(s);
    return;
  }

  if (Check(TokenKind::kKwImport)) {
    std::vector<ModuleItem*> import_items;
    ParseImportDecl(import_items);
    for (auto* imp : import_items) {
      auto* s = arena_.Create<Stmt>();
      s->kind = StmtKind::kBlockItemDecl;
      s->range.start = imp->loc;
      s->decl_item = imp;
      s->attrs = attrs;
      stmts.push_back(s);
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
      s->attrs = attrs;
      stmts.push_back(s);
    }
    return;
  }
  ParseBlockDataDecl(stmts, attrs);
}

}  // namespace delta
