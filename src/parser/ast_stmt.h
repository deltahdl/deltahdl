#pragma once

#include <cstdint>
#include <string_view>
#include <utility>
#include <vector>

#include "common/source_loc.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"

namespace delta {

enum class StmtKind : uint8_t {
  kBlock,
  kIf,
  kCase,
  kFor,
  kForeach,
  kWhile,
  kForever,
  kRepeat,
  kDoWhile,
  kBreak,
  kContinue,
  kReturn,
  kBlockingAssign,
  kNonblockingAssign,
  kExprStmt,
  kTimingControl,
  kDelay,
  kEventControl,
  kWait,
  kWaitFork,
  kFork,
  kDisable,
  kDisableFork,
  kEventTrigger,
  kNbEventTrigger,
  kNull,
  kAssign,
  kDeassign,
  kForce,
  kRelease,
  kAssertImmediate,
  kAssumeImmediate,
  kCoverImmediate,
  kWaitOrder,
  kRandcase,
  kRandsequence,
  kVarDecl,
  kBlockItemDecl,
  kCycleDelay,
  kExpect,

};

enum class Edge : uint8_t {
  kNone,
  kPosedge,
  kNegedge,
  kEdge,
};

struct ModuleItem;

// §16.12: a property_expr built from the operands the evaluation reads --
// a boolean, a sequence weak or strong (§16.12.2) -- under the operators
// not (§16.12.3), or (§16.12.4), and (§16.12.5), if-else (§16.12.6),
// implication (§16.12.7), implies and iff (§16.12.8), the last two over two
// operands, nexttime (§16.12.10), `strong` where it is s_nexttime and its
// tick count, one where none was written, in `boolean`, always
// (§16.12.11), `strong` where it is s_always, over the range below,
// eventually (§16.12.13) likewise, `strong` where it is s_eventually, the
// aborts (§16.12.14) over one operand, and until (§16.12.12) over two
// operands, `strong` where it is s_until or
// s_until_with and `range_unbounded` where it is an overlapping form,
// until_with or s_until_with. A boolean leaf
// carries `boolean`, a sequence leaf
// `sequence` and `strong`, an operator its operands, an if-else its
// condition in `boolean` with the then and else properties as its operands,
// the else absent where none was written, and an implication its antecedent
// in `sequence`, `strong` where it is the nonoverlapped `|=>`, with the
// consequent as its one operand.
struct PropertyExprNode {
  enum class Kind : uint8_t {
    kBoolean,
    kSequence,
    kNot,
    kOr,
    kAnd,
    kIfElse,
    kImplication,
    kImplies,
    kIff,
    kNexttime,
    kAlways,
    kUntil,
    kEventually,
    kAbort,
    kCase
  };
  Kind kind = Kind::kBoolean;
  Expr* boolean = nullptr;
  ModuleItem* sequence = nullptr;
  bool strong = false;
  std::vector<PropertyExprNode*> operands;
  // §16.12.11: the range of ticks an always covers, from `range_min` to
  // `range_max` after the attempt's tick, `range_unbounded` where the
  // maximum is `$` or no range was written; the minimum null where none
  // was written stands for 0.
  Expr* range_min = nullptr;
  Expr* range_max = nullptr;
  bool range_unbounded = false;
  // §16.12.14: an abort over its one operand, its condition in `boolean`,
  // `accept` where it is accept_on or sync_accept_on and `synchronous` where
  // it is one of the sync_ forms, checked at the clock ticks alone.
  bool accept = false;
  bool synchronous = false;
  // §16.12.16: a case over the case expression in `boolean`, each operand
  // the property of one property_case_item and the item's expressions at
  // the same index here, the default's none.
  std::vector<std::vector<Expr*>> case_values;
};

struct EventExpr {
  Edge edge = Edge::kNone;
  Expr* signal = nullptr;
  Expr* iff_condition = nullptr;
  bool is_sequence_event = false;
};

struct CaseItem {
  std::vector<Expr*> patterns;
  Stmt* body = nullptr;
  bool is_default = false;
};

enum class CaseQualifier : uint8_t {
  kNone,
  kUnique,
  kUnique0,
  kPriority,
};

enum class RsProdKind : uint8_t {
  kItem,
  kCodeBlock,
  kIf,
  kRepeat,
  kCase,
};

struct RsProductionItem {
  std::string_view name;
  std::vector<Expr*> args;
  // §18.17: where the identifier this item names stands, so a report about the
  // name is made at the name. Nothing else on the path from a randsequence
  // statement to a production identifier carries a location -- RsCaseItem,
  // RsProd, RsRule and RsProduction hold none -- so every such report used to
  // stand at the randsequence keyword, and a statement whose rules misspell two
  // names produced two reports on one line with nothing to tell them apart.
  //
  // Parser::ParseRsProductionItem fills it from the identifier token it was
  // already reading. An item that is default-constructed rather than parsed
  // carries no name either, and CheckProductionItem in
  // elaborator_validate_randsequence.cpp returns on that before reading this.
  SourceLoc loc;
};

struct RsCaseItem {
  std::vector<Expr*> patterns;
  RsProductionItem item;
  bool is_default = false;
};

struct RsProd {
  RsProdKind kind = RsProdKind::kItem;
  RsProductionItem item;
  std::vector<Stmt*> code_stmts;
  Expr* condition = nullptr;
  RsProductionItem if_true;
  RsProductionItem if_false;
  bool has_else = false;
  Expr* repeat_count = nullptr;
  RsProductionItem repeat_item;
  Expr* case_expr = nullptr;
  std::vector<RsCaseItem> case_items;
};

struct RsRule {
  std::vector<RsProd> prods;
  bool is_rand_join = false;
  Expr* rand_join_expr = nullptr;
  std::vector<RsProductionItem> rand_join_items;
  Expr* weight = nullptr;
  std::vector<Stmt*> weight_code;
};

struct RsProduction {
  std::string_view name;
  // §18.17.7: a production may carry a data_type_or_void return type and a
  // tf_port_list of formal arguments. has_return_type records that a
  // data_type_or_void was written (including an explicit 'void'); return_type
  // holds the parsed type so the value-passing engine can size the production's
  // return value. ports holds the parsed formal arguments (empty when none).
  bool has_return_type = false;
  bool has_ports = false;
  DataType return_type;
  std::vector<FunctionArg> ports;
  std::vector<RsRule> rules;
};

struct Stmt {
  StmtKind kind;
  SourceRange range;
  std::vector<Attribute> attrs;
  std::string_view label;
  CaseQualifier qualifier = CaseQualifier::kNone;

  std::vector<Stmt*> stmts;

  Expr* condition = nullptr;
  Stmt* then_branch = nullptr;
  Stmt* else_branch = nullptr;

  Expr* lhs = nullptr;
  Expr* rhs = nullptr;
  Expr* delay = nullptr;
  Expr* cycle_delay = nullptr;

  std::vector<Stmt*> for_inits;
  Expr* for_cond = nullptr;
  std::vector<Stmt*> for_steps;
  Stmt* for_body = nullptr;
  std::vector<DataType> for_init_types;

  std::vector<CaseItem> case_items;
  TokenKind case_kind = TokenKind::kKwCase;
  bool case_inside = false;
  bool case_matches = false;

  std::vector<EventExpr> events;
  bool is_star_event = false;
  Expr* repeat_event_count = nullptr;

  std::vector<Stmt*> fork_stmts;
  TokenKind join_kind = TokenKind::kKwJoin;

  Expr* expr = nullptr;

  Stmt* body = nullptr;

  std::vector<std::string_view> foreach_vars;

  Expr* assert_expr = nullptr;
  // §16.12: the disable condition of a concurrent assertion's property_spec,
  // `disable iff ( expression )`, read live at each attempt; an attempt at
  // which it is true is disabled, neither succeeding nor failing.
  Expr* assert_disable_iff = nullptr;
  // §16.12.2: a sequential property, the sequence_expr of a concurrent
  // assertion's property_spec read as a linear sequence body, and whether it
  // is `strong(...)`, so that an attempt still in flight when the run ends
  // fails; a weak one, written `weak(...)` or bare in an assert or assume,
  // never fails that way, and a cover statement's is strong. `assert_expr`
  // is unset where this is set.
  ModuleItem* assert_sequence = nullptr;
  bool assert_strong = false;
  // §16.12.3: the property is `not` the boolean or sequence carried, so each
  // attempt's result is the opposite of the underlying one, the strength of
  // a sequence switched with it.
  bool assert_negated = false;
  // §16.12.4 and §16.12.5: the property as a tree of the operands above
  // under or and and, set where the property_spec holds either operator;
  // the fields above then stand unset but for the placeholder.
  PropertyExprNode* assert_property = nullptr;
  Stmt* assert_pass_stmt = nullptr;
  Stmt* assert_fail_stmt = nullptr;
  bool is_deferred = false;

  bool is_final_deferred = false;

  bool is_procedural_concurrent = false;

  // §16.5: "The keyword property distinguishes a concurrent assertion from an
  // immediate assertion." Set on the immediate-assert statement the parser
  // synthesises for the clocked boolean form of `assert property (@(clk) e)`,
  // which is the only thing that tells that body apart from an `assert (e)`
  // written inside an always_ff: §16.5.1 samples the expressions of the first
  // and leaves the second reading the values standing now.
  bool is_concurrent_clocked = false;

  std::vector<Expr*> wait_order_events;

  std::vector<std::pair<Expr*, Stmt*>> randcase_items;

  std::string_view rs_top_production;
  std::vector<RsProduction> rs_productions;

  DataType var_decl_type;
  std::string_view var_name;
  std::vector<Expr*> var_unpacked_dims;
  Expr* var_init = nullptr;
  bool var_is_automatic = false;
  bool var_is_static = false;
  bool var_is_const = false;

  ModuleItem* decl_item = nullptr;
};

// The subroutine call an expression statement consists of, or nullptr where
// the statement is not one: A.6.9's subroutine_call_statement is the call
// itself or `void'(function_subroutine_call)`, which §13.4.1 has discard a
// nonvoid function's result, so a void cast is seen through to the call it
// wraps. §16.4 states its action-block rule over this statement, and its
// readers look at the call rather than at the cast.
inline const Expr* SubroutineCallOfStmt(const Stmt* stmt) {
  if (stmt == nullptr || stmt->kind != StmtKind::kExprStmt) return nullptr;
  const Expr* e = stmt->expr;
  if (e != nullptr && e->kind == ExprKind::kCast && e->text == "void") {
    e = e->lhs;
  }
  if (e == nullptr) return nullptr;
  if (e->kind != ExprKind::kCall && e->kind != ExprKind::kSystemCall) {
    return nullptr;
  }
  return e;
}

}  // namespace delta
