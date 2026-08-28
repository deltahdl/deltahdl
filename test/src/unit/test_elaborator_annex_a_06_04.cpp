// A.6.4's statement productions, together with A.6.5's timing controls,
// A.6.7's case statements and A.6.12's randsequence, decide which positions a
// statement holds another statement in and which it holds an expression in.
// src/elaborator/elaborator_validate_internal.h states each of those two lists
// exactly once, as ForEachChildStmt and ForEachChildExpr, so that every
// elaborator walk runs its rule over the same positions rather than over the
// ones its author remembered.
//
// These two cases are what fails when a member is added to Stmt, reaches the
// parser, and does not reach the helper. Every other test of a walk asks
// whether one rule holds at one position; only these ask whether the shared
// list is the whole list, which is the failure that makes every walk wrong at
// once. #3301 and #3303 each ask for one, having each found walks that had
// silently exempted a construct from a rule.
//
// Each case names every position rather than counting them. A count says a
// visit went missing and not which, so the report would name the number of
// positions instead of the member that was dropped; a set of names makes the
// failure read as the member.

#include <set>
#include <string>
#include <string_view>
#include <vector>

#include "elaborator/elaborator_validate_internal.h"
#include "fixture_elaborator.h"
#include "parser/ast.h"

using namespace delta;

namespace {

// One statement per position ForEachChildStmt is required to reach, each
// labelled with the member it stands in. Held by value so the addresses stay
// good for the walk, and referenced from `s` by pointer as the parser would.
struct StmtTreeWithEveryChildStatement {
  Stmt owner;
  Stmt stmts;
  Stmt fork_stmts;
  Stmt for_inits;
  Stmt for_steps;
  Stmt then_branch;
  Stmt else_branch;
  Stmt body;
  Stmt for_body;
  Stmt assert_pass_stmt;
  Stmt assert_fail_stmt;
  Stmt case_item_body;
  Stmt randcase_item_body;
  Stmt rs_prod_code_stmt;
  Stmt rs_rule_weight_code_stmt;

  StmtTreeWithEveryChildStatement() {
    stmts.label = "stmts";
    fork_stmts.label = "fork_stmts";
    for_inits.label = "for_inits";
    for_steps.label = "for_steps";
    then_branch.label = "then_branch";
    else_branch.label = "else_branch";
    body.label = "body";
    for_body.label = "for_body";
    assert_pass_stmt.label = "assert_pass_stmt";
    assert_fail_stmt.label = "assert_fail_stmt";
    case_item_body.label = "case_items[].body";
    randcase_item_body.label = "randcase_items[].second";
    rs_prod_code_stmt.label = "rs_productions RsProd::code_stmts";
    rs_rule_weight_code_stmt.label = "rs_productions RsRule::weight_code";

    owner.stmts.push_back(&stmts);
    owner.fork_stmts.push_back(&fork_stmts);
    owner.for_inits.push_back(&for_inits);
    owner.for_steps.push_back(&for_steps);
    owner.then_branch = &then_branch;
    owner.else_branch = &else_branch;
    owner.body = &body;
    owner.for_body = &for_body;
    owner.assert_pass_stmt = &assert_pass_stmt;
    owner.assert_fail_stmt = &assert_fail_stmt;

    CaseItem ci;
    ci.body = &case_item_body;
    owner.case_items.push_back(ci);

    owner.randcase_items.emplace_back(nullptr, &randcase_item_body);

    RsProd prod;
    prod.code_stmts.push_back(&rs_prod_code_stmt);
    RsRule rule;
    rule.prods.push_back(prod);
    rule.weight_code.push_back(&rs_rule_weight_code_stmt);
    RsProduction production;
    production.rules.push_back(rule);
    owner.rs_productions.push_back(production);
  }
};

// A.6.4 and its neighbours admit a statement in fourteen positions of Stmt,
// which is the thirteen members src/parser/ast_stmt.h declares counting
// rs_productions as the two lists A.6.12 reaches through it: an rs_prod may be
// a code block and a weight_specification may be followed by one.
TEST(StatementChildPositions, ForEachChildStmtVisitsEveryStatementPosition) {
  StmtTreeWithEveryChildStatement tree;
  std::set<std::string> visited;
  ForEachChildStmt(&tree.owner, [&](Stmt* const& sub) {
    if (sub != nullptr) visited.insert(std::string(sub->label));
  });

  const std::set<std::string> kExpected{"assert_fail_stmt",
                                        "assert_pass_stmt",
                                        "body",
                                        "case_items[].body",
                                        "else_branch",
                                        "for_body",
                                        "for_inits",
                                        "for_steps",
                                        "fork_stmts",
                                        "randcase_items[].second",
                                        "rs_productions RsProd::code_stmts",
                                        "rs_productions RsRule::weight_code",
                                        "stmts",
                                        "then_branch"};
  EXPECT_EQ(visited, kExpected);
}

// One expression per position ForEachChildExpr is required to reach, each
// carrying the member it stands in as its text.
struct StmtTreeWithEveryChildExpression {
  Stmt owner;
  std::vector<Expr> exprs;

  // Returns a pointer to a fresh Expr tagged with `where`. The vector is
  // reserved up front so that no push_back reallocates and invalidates a
  // pointer already handed out.
  Expr* Make(std::string_view where) {
    exprs.emplace_back();
    exprs.back().text = where;
    return &exprs.back();
  }

  StmtTreeWithEveryChildExpression() {
    exprs.reserve(32);
    owner.condition = Make("condition");
    owner.lhs = Make("lhs");
    owner.rhs = Make("rhs");
    owner.delay = Make("delay");
    owner.cycle_delay = Make("cycle_delay");
    owner.for_cond = Make("for_cond");
    owner.expr = Make("expr");
    owner.assert_expr = Make("assert_expr");
    owner.repeat_event_count = Make("repeat_event_count");
    owner.var_init = Make("var_init");

    EventExpr ev;
    ev.signal = Make("events[].signal");
    ev.iff_condition = Make("events[].iff_condition");
    owner.events.push_back(ev);

    owner.wait_order_events.push_back(Make("wait_order_events"));
    owner.randcase_items.emplace_back(Make("randcase_items[].first"), nullptr);

    CaseItem ci;
    ci.patterns.push_back(Make("case_items[].patterns"));
    owner.case_items.push_back(ci);

    owner.var_unpacked_dims.push_back(Make("var_unpacked_dims"));

    RsProd prod;
    prod.condition = Make("RsProd::condition");
    prod.repeat_count = Make("RsProd::repeat_count");
    prod.case_expr = Make("RsProd::case_expr");
    prod.item.args.push_back(Make("RsProd::item args"));
    prod.if_true.args.push_back(Make("RsProd::if_true args"));
    prod.if_false.args.push_back(Make("RsProd::if_false args"));
    prod.repeat_item.args.push_back(Make("RsProd::repeat_item args"));
    RsCaseItem rs_ci;
    rs_ci.patterns.push_back(Make("RsCaseItem::patterns"));
    rs_ci.item.args.push_back(Make("RsCaseItem::item args"));
    prod.case_items.push_back(rs_ci);

    RsRule rule;
    rule.prods.push_back(prod);
    rule.weight = Make("RsRule::weight");
    rule.rand_join_expr = Make("RsRule::rand_join_expr");
    RsProductionItem join_item;
    join_item.args.push_back(Make("RsRule::rand_join_items args"));
    rule.rand_join_items.push_back(join_item);

    RsProduction production;
    production.rules.push_back(rule);
    owner.rs_productions.push_back(production);
  }
};

// The counterpart claim for expressions. src/parser/ast_stmt.h declares ten
// scalar Expr* members of Stmt and reaches six further positions through
// members it holds, and A.6.12 reaches eleven more inside a randsequence, none
// of which is a statement and so none of which ForEachChildStmt above answers
// for.
TEST(StatementChildPositions, ForEachChildExprVisitsEveryExpressionPosition) {
  StmtTreeWithEveryChildExpression tree;
  std::set<std::string> visited;
  ForEachChildExpr(&tree.owner, [&](Expr* const& e) {
    if (e != nullptr) visited.insert(std::string(e->text));
  });

  const std::set<std::string> kExpected{"RsCaseItem::item args",
                                        "RsCaseItem::patterns",
                                        "RsProd::case_expr",
                                        "RsProd::condition",
                                        "RsProd::if_false args",
                                        "RsProd::if_true args",
                                        "RsProd::item args",
                                        "RsProd::repeat_count",
                                        "RsProd::repeat_item args",
                                        "RsRule::rand_join_expr",
                                        "RsRule::rand_join_items args",
                                        "RsRule::weight",
                                        "assert_expr",
                                        "case_items[].patterns",
                                        "condition",
                                        "cycle_delay",
                                        "delay",
                                        "events[].iff_condition",
                                        "events[].signal",
                                        "expr",
                                        "for_cond",
                                        "lhs",
                                        "randcase_items[].first",
                                        "repeat_event_count",
                                        "rhs",
                                        "var_init",
                                        "var_unpacked_dims",
                                        "wait_order_events"};
  EXPECT_EQ(visited, kExpected);
}

}  // namespace
