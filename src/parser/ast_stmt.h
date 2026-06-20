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
  Stmt* assert_pass_stmt = nullptr;
  Stmt* assert_fail_stmt = nullptr;
  bool is_deferred = false;

  bool is_final_deferred = false;

  bool is_procedural_concurrent = false;

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

}  // namespace delta
