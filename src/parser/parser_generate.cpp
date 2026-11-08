#include <format>
#include <string_view>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/expr_parser_internal.h"
#include "parser/parser.h"
#include "parser/parser_type_name_scope.h"

namespace delta {

static bool ClosesGenerateRegionEnclosure(TokenKind tk) {
  return tk == TokenKind::kKwEndmodule || tk == TokenKind::kKwEndinterface ||
         tk == TokenKind::kKwEndprogram || tk == TokenKind::kKwEndchecker;
}

static bool ClosesGenerateBlockEnclosure(TokenKind tk) {
  return ClosesGenerateRegionEnclosure(tk) || tk == TokenKind::kKwEndgenerate ||
         tk == TokenKind::kKwEndcase;
}

static bool EndsGenerateBlockItems(TokenKind tk, bool else_may_follow) {
  return ClosesGenerateBlockEnclosure(tk) ||
         (else_may_follow && tk == TokenKind::kKwElse);
}

void Parser::ParseGenerateItem(std::vector<ModuleItem*>& items) {
  bool design_element = Check(TokenKind::kKwModule) ||
                        Check(TokenKind::kKwMacromodule) ||
                        Check(TokenKind::kKwProgram) ||
                        (Check(TokenKind::kKwInterface) && !IsAtClassDecl());
  if (design_element) {
    diag_.Error(CurrentLoc(),
                std::format("'{}' declares a design element, which is not an "
                            "item of a generate block or region",
                            CurrentToken().text),
                Subclause("27.3"));
  }
  ParseModuleItem(items);
}

void Parser::ParseGenerateBody(std::vector<ModuleItem*>& body,
                               std::string_view& out_label,
                               bool& out_has_begin_end, bool else_may_follow) {
  struct DepthGuard {
    int& d;
    explicit DepthGuard(int& d) : d(d) { ++d; }
    ~DepthGuard() { --d; }
  } guard(generate_block_depth_);

  TypeNameScope type_scope(*this);

  out_has_begin_end = false;

  if (Match(TokenKind::kSemicolon)) return;

  auto detect_gen_label = [&]() -> bool {
    if (!CheckIdentifier()) return false;
    auto saved = lexer_.SavePos();
    auto ident = Consume();
    bool committed = Match(TokenKind::kColon) && Check(TokenKind::kKwBegin);
    if (!committed) {
      lexer_.RestorePos(saved);
      return false;
    }
    out_label = ident.text;
    return true;
  };
  bool has_gen_label = detect_gen_label();

  if (!Match(TokenKind::kKwBegin)) {
    ParseGenerateItem(body);
    return;
  }
  out_has_begin_end = true;

  if (has_gen_label && Check(TokenKind::kColon)) {
    diag_.Error(CurrentLoc(),
                "cannot have both a generate block label and a block name",
                Subclause("9.3.5"));
  } else if (!has_gen_label && Match(TokenKind::kColon) && CheckIdentifier()) {
    out_label = Consume().text;
  }

  while (!Check(TokenKind::kKwEnd) && !AtEnd() &&
         !EndsGenerateBlockItems(CurrentToken().kind, else_may_follow)) {
    ParseGenerateItem(body);
  }
  Expect(TokenKind::kKwEnd, Subclause("27.3"));
  MatchEndBlockLabel(out_label, {});
}

void Parser::ParseGenerateRegion(std::vector<ModuleItem*>& items) {
  auto loc = CurrentLoc();
  RejectInPackageBody("a generate region is not an item of a package");
  Expect(TokenKind::kKwGenerate, Subclause("27.3"));

  if (in_generate_region_) {
    diag_.Error(
        loc,
        "this generate region opens inside another one, which is not allowed",
        Subclause("27.3"));
  } else if (InGenerateBlock()) {
    diag_.Error(loc,
                "this generate region opens inside a generate block; a "
                "generate region stands only directly in a module",
                Subclause("27.3"));
  }
  bool saved = in_generate_region_;
  in_generate_region_ = true;
  while (!Check(TokenKind::kKwEndgenerate) && !AtEnd() &&
         !ClosesGenerateRegionEnclosure(CurrentToken().kind)) {
    ParseGenerateItem(items);
  }
  in_generate_region_ = saved;
  Expect(TokenKind::kKwEndgenerate, Subclause("27.3"));
}

Stmt* Parser::ParseGenvarInitialization() {
  bool declares_genvar = Match(TokenKind::kKwGenvar);
  auto saved = lexer_.SavePos();
  bool is_assignment = CheckIdentifier();
  if (is_assignment) {
    Consume();
    is_assignment = Check(TokenKind::kEq);
  }
  lexer_.RestorePos(saved);
  auto* init = arena_.Create<Stmt>();
  init->kind = StmtKind::kBlockingAssign;
  init->range.start = CurrentLoc();
  if (!is_assignment) {
    diag_.Error(CurrentLoc(),
                "a loop generate's initialization is written "
                "'[ genvar ] genvar_identifier = constant_expression'",
                Subclause("A.4.2"));
    ParseAssignmentOrExprStmt();
    init->lhs = MakeIdentifierNode(arena_, "", init->range.start);
    return init;
  }
  Token id = Consume();
  init->lhs = MakeIdentifierNode(arena_, id.text, id.loc);
  if (declares_genvar) init->var_name = id.text;
  Consume();
  init->rhs = ParseExpr();
  Expect(TokenKind::kSemicolon, Subclause("27.4"));
  return init;
}

static bool IsGenvarIteration(const Stmt* step) {
  if (step->kind == StmtKind::kBlockingAssign) {
    return step->lhs != nullptr && step->lhs->kind == ExprKind::kIdentifier;
  }
  if (step->kind != StmtKind::kExprStmt || step->expr == nullptr) return false;
  const Expr* e = step->expr;
  bool inc_or_dec =
      (e->kind == ExprKind::kUnary || e->kind == ExprKind::kPostfixUnary) &&
      (e->op == TokenKind::kPlusPlus || e->op == TokenKind::kMinusMinus);
  return inc_or_dec && e->lhs != nullptr &&
         e->lhs->kind == ExprKind::kIdentifier;
}

Stmt* Parser::ParseGenvarIteration(std::string_view genvar) {
  SourceLoc loc = CurrentLoc();
  Stmt* step = ParseAssignmentOrExprNoSemi();
  if (IsGenvarIteration(step)) return step;
  diag_.Error(loc,
              "a loop generate's iteration is written 'genvar_identifier "
              "assignment_operator genvar_expression', 'inc_or_dec_operator "
              "genvar_identifier' or 'genvar_identifier inc_or_dec_operator'",
              Subclause("A.4.2"));
  auto* increment = arena_.Create<Expr>();
  increment->kind = ExprKind::kPostfixUnary;
  increment->op = TokenKind::kPlusPlus;
  increment->lhs = MakeIdentifierNode(arena_, genvar, loc);
  increment->range.start = loc;
  auto* recorded = arena_.Create<Stmt>();
  recorded->kind = StmtKind::kExprStmt;
  recorded->range.start = loc;
  recorded->expr = increment;
  return recorded;
}

ModuleItem* Parser::ParseGenerateFor() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kGenerateFor;
  item->loc = CurrentLoc();
  Expect(TokenKind::kKwFor, Subclause("27.4"));
  Expect(TokenKind::kLParen, Subclause("27.4"));
  item->gen_init = ParseGenvarInitialization();
  item->gen_cond = ParseExpr();
  Expect(TokenKind::kSemicolon, Subclause("27.4"));
  item->gen_step = ParseGenvarIteration(item->gen_init->lhs->text);
  Expect(TokenKind::kRParen, Subclause("27.4"));
  ParseGenerateBody(item->gen_body, item->name, item->gen_body_has_begin_end,
                    false);
  return item;
}

ModuleItem* Parser::ParseGenerateIf() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kGenerateIf;
  item->loc = CurrentLoc();
  Expect(TokenKind::kKwIf, Subclause("27.5"));
  Expect(TokenKind::kLParen, Subclause("27.5"));
  item->gen_cond = ParseExpr();
  Expect(TokenKind::kRParen, Subclause("27.5"));
  ParseGenerateBody(item->gen_body, item->name, item->gen_body_has_begin_end,
                    true);
  if (!Match(TokenKind::kKwElse)) return item;
  if (Check(TokenKind::kKwIf)) {
    item->gen_else = ParseGenerateIf();
  } else {
    auto* else_item = arena_.Create<ModuleItem>();
    else_item->kind = ModuleItemKind::kGenerateIf;
    else_item->loc = CurrentLoc();
    ParseGenerateBody(else_item->gen_body, else_item->name,
                      else_item->gen_body_has_begin_end, false);
    item->gen_else = else_item;
  }
  return item;
}

void Parser::ParseGenerateCaseLabel(GenerateCaseItem& ci) {
  if (Match(TokenKind::kKwDefault)) {
    ci.is_default = true;
    Match(TokenKind::kColon);
    return;
  }
  ci.patterns.push_back(ParseExpr());
  while (Match(TokenKind::kComma)) {
    ci.patterns.push_back(ParseExpr());
  }
  Expect(TokenKind::kColon, Subclause("27.5"));
}

ModuleItem* Parser::ParseGenerateCase() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kGenerateCase;
  item->loc = CurrentLoc();
  Expect(TokenKind::kKwCase, Subclause("27.5"));
  Expect(TokenKind::kLParen, Subclause("27.5"));
  item->gen_cond = ParseExpr();
  Expect(TokenKind::kRParen, Subclause("27.5"));
  while (!Check(TokenKind::kKwEndcase) && !AtEnd()) {
    GenerateCaseItem ci;
    ParseGenerateCaseLabel(ci);
    ParseGenerateBody(ci.body, ci.label, ci.has_begin_end, false);
    item->gen_case_items.push_back(std::move(ci));
  }
  if (item->gen_case_items.empty()) {
    diag_.Error(CurrentLoc(),
                "a case generate construct has at least one "
                "case_generate_item",
                Subclause("A.4.2"));
  }
  Expect(TokenKind::kKwEndcase, Subclause("27.5"));
  return item;
}

}  // namespace delta
