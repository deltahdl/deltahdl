#include <algorithm>
#include <cstddef>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "lexer/token.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"
#include "parser/parser.h"
#include "parser/parser_data_decl_internal.h"

namespace delta {

namespace {

bool IsTfPortDirectionKw(TokenKind tk) {
  return tk == TokenKind::kKwInput || tk == TokenKind::kKwOutput ||
         tk == TokenKind::kKwInout || tk == TokenKind::kKwRef ||
         tk == TokenKind::kKwConst;
}

void DefaultImplicitToLogic(DataType& dt) {
  if (dt.kind == DataTypeKind::kImplicit) dt.kind = DataTypeKind::kLogic;
}

}  // namespace

struct TfPortHeader {
  Direction dir = Direction::kInput;
  bool is_const = false;
  bool is_ref_static = false;
  DataType dt;
};

Direction Parser::ParseTfPortDirection() {
  if (Check(TokenKind::kKwInput)) {
    Consume();
    return Direction::kInput;
  }
  if (Check(TokenKind::kKwOutput)) {
    Consume();
    return Direction::kOutput;
  }
  if (Check(TokenKind::kKwInout)) {
    Consume();
    return Direction::kInout;
  }
  Consume();
  return Direction::kRef;
}

void Parser::ParseTfPortDeclarators(ModuleItem* item, const TfPortHeader& hdr) {
  do {
    FunctionArg arg;
    arg.is_const = hdr.is_const;
    arg.is_ref_static = hdr.is_ref_static;
    arg.direction = hdr.dir;
    arg.data_type = hdr.dt;
    arg.name = Expect(TokenKind::kIdentifier, Subclause("13.3")).text;
    ParseUnpackedDims(arg.unpacked_dims);
    if (Match(TokenKind::kEq)) {
      arg.default_value = ParseExpr();
    }
    item->func_args.push_back(arg);
  } while (Match(TokenKind::kComma));
  Expect(TokenKind::kSemicolon, Subclause("13.3"));
}

bool Parser::IsTfPortDeclarationStart() {
  auto tk = CurrentToken().kind;
  if (tk != TokenKind::kKwConst) return IsTfPortDirectionKw(tk);
  auto saved = lexer_.SavePos();
  Consume();
  bool qualifies_ref = Check(TokenKind::kKwRef);
  lexer_.RestorePos(saved);
  return qualifies_ref;
}

bool Parser::TryParseTfPortDeclaration(
    ModuleItem* item, std::unordered_set<std::string_view>& untyped) {
  auto saved = lexer_.SavePos();
  diag_.PushSuppress();
  ParseAttributes();
  bool opens = IsTfPortDeclarationStart();
  diag_.PopSuppress();
  lexer_.RestorePos(saved);
  if (!opens) return false;
  ParseAttributes();
  TfPortHeader hdr;
  hdr.is_const = Match(TokenKind::kKwConst);
  hdr.dir = ParseTfPortDirection();
  hdr.is_ref_static =
      (hdr.dir == Direction::kRef) && Match(TokenKind::kKwStatic);
  bool has_var = Match(TokenKind::kKwVar);
  bool implicit_type = false;
  if (!ParserDataDeclHelpers::ReadKeyedTypeReference(*this, hdr.dt, has_var,
                                                     false)) {
    hdr.dt = ParseDeclaredDataType();
    implicit_type = hdr.dt.kind == DataTypeKind::kImplicit;
    if (implicit_type) ParsePackedDims(hdr.dt);
    DefaultImplicitToLogic(hdr.dt);
  }

  size_t first = item->func_args.size();
  ParseTfPortDeclarators(item, hdr);
  if (implicit_type) {
    for (size_t i = first; i < item->func_args.size(); ++i) {
      untyped.insert(item->func_args[i].name);
    }
  }
  return true;
}

static void TypeFormalsFromBodyDecls(
    ModuleItem* item, size_t first,
    std::unordered_set<std::string_view>& untyped) {
  auto& stmts = item->func_body_stmts;
  for (size_t i = first; i < stmts.size();) {
    const Stmt* decl = stmts[i];
    if (decl->kind != StmtKind::kVarDecl || decl->var_is_param ||
        decl->var_init != nullptr || untyped.erase(decl->var_name) == 0) {
      ++i;
      continue;
    }
    auto formal =
        std::ranges::find(item->func_args, decl->var_name, &FunctionArg::name);
    formal->data_type = decl->var_decl_type;
    formal->unpacked_dims = decl->var_unpacked_dims;
    stmts.erase(stmts.begin() + static_cast<std::ptrdiff_t>(i));
  }
}

static void ReportDeclarationAfterStatement(DiagEngine& diag, SourceLoc loc,
                                            TokenKind end_kw) {
  if (end_kw == TokenKind::kKwEndtask) {
    diag.Error(loc, "a declaration cannot follow a statement in a task body",
               Subclause("13.3"));
    return;
  }
  diag.Error(loc, "a declaration cannot follow a statement in a function body",
             Subclause("13.4"));
}

void Parser::ParseSubroutineBody(ModuleItem* item, TokenKind end_kw,
                                 Subclause subclause) {
  std::unordered_set<std::string_view> untyped;
  bool before_stmts = true;
  while (!Check(end_kw) && !AtEnd()) {
    SourceLoc loc = CurrentLoc();
    if (TryParseTfPortDeclaration(item, untyped)) {
      if (item->is_ansi_ports) {
        diag_.Error(loc,
                    "a task or function whose ports are listed in parentheses "
                    "cannot declare a port in its body",
                    subclause);
      } else if (!before_stmts) {
        diag_.Error(loc,
                    "a port declaration cannot follow a statement in a task "
                    "or function body",
                    subclause);
      }
      continue;
    }
    if (IsBlockVarDeclStart()) {
      if (!before_stmts) ReportDeclarationAfterStatement(diag_, loc, end_kw);
      size_t first = item->func_body_stmts.size();
      ParseBlockVarDecls(item->func_body_stmts);
      TypeFormalsFromBodyDecls(item, first, untyped);
    } else if (!RejectMisplacedStmtLabel()) {
      before_stmts = false;
      item->func_body_stmts.push_back(ParseStmt());
    }
  }
}

}  // namespace delta
