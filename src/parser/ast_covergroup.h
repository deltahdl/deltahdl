#pragma once

#include <cstdint>
#include <string_view>
#include <vector>

#include "common/source_loc.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

// The entities of A.2.11, Covergroup declarations, as the parser reads them.
// Each struct holds one production of that annex and is named after it; an
// expression the grammar calls a covergroup_expression is held as an Expr,
// since A.2.11 makes it an expression (§19.5 restricts what it may name).

// A.2.11 coverage_option: `option . member = expression` or `type_option .
// member = constant_expression` (§19.7, §19.7.1).
struct CoverageOption {
  bool is_type_option = false;
  std::string_view member;
  SourceLoc loc;
  Expr* value = nullptr;
};

// A.2.11 covergroup_value_range: one value, `[ lo : hi ]` with either bound
// `$`, or `[ center +/- tolerance ]` and `[ center +%- percent ]` (§19.5.1).
enum class CovergroupValueRangeKind : uint8_t {
  kValue,
  kRange,
  kAbsoluteTolerance,
  kRelativeTolerance,
};

struct CovergroupValueRange {
  CovergroupValueRangeKind kind = CovergroupValueRangeKind::kValue;
  // The value, or the low bound, center or base; null for a `$` low bound.
  Expr* lo = nullptr;
  // The high bound, tolerance or percent; null for a `$` high bound and for a
  // single value.
  Expr* hi = nullptr;
};

// The repetition A.2.11's trans_range_list may put after its trans_item:
// consecutive `[* r ]`, goto `[-> r ]` or nonconsecutive `[= r ]` (§19.5.2).
enum class TransRepetition : uint8_t {
  kNone,
  kConsecutive,
  kGoto,
  kNonconsecutive,
};

// A.2.11 trans_range_list: a trans_item, a covergroup_range_list, and the
// repeat_range of its repetition, `lo` alone or `lo : hi`.
struct TransRangeList {
  std::vector<CovergroupValueRange> items;
  TransRepetition repetition = TransRepetition::kNone;
  Expr* repeat_lo = nullptr;
  Expr* repeat_hi = nullptr;
};

// A.2.11 trans_set: trans_range_lists joined by `=>`, one per sample point.
struct TransSet {
  SourceLoc loc;
  std::vector<TransRangeList> steps;
};

// A.2.11 bins_keyword.
enum class BinsKeyword : uint8_t { kBins, kIllegalBins, kIgnoreBins };

// The alternative of A.2.11's bins_or_options an item takes.
enum class BinsOrOptionsKind : uint8_t {
  kOption,
  // `= { covergroup_range_list } [ with ( ... ) ]` (§19.5.1, §19.5.1.1).
  kValues,
  // `= cover_point_identifier with ( ... )` (§19.5.1.1).
  kCoverPointWith,
  // `= set_covergroup_expression` (§19.5.1.2).
  kSetExpression,
  // `= trans_list` (§19.5.2).
  kTransitions,
  // `= default` (§19.5).
  kDefault,
  // `= default sequence` (§19.5.2).
  kDefaultSequence,
};

// A.2.11 bins_or_options: a coverage_option, or one bins declaration of a
// coverpoint.
struct BinsOrOptions {
  BinsOrOptionsKind kind = BinsOrOptionsKind::kValues;
  SourceLoc loc;
  CoverageOption option;
  bool wildcard = false;
  BinsKeyword keyword = BinsKeyword::kBins;
  std::string_view name;
  // `name [ ]` or `name [ size ]`: is_array with a null or written size.
  bool is_array = false;
  Expr* array_size = nullptr;
  std::vector<CovergroupValueRange> ranges;
  std::string_view with_cover_point;
  Expr* with_expr = nullptr;
  Expr* set_expr = nullptr;
  std::vector<TransSet> transitions;
  Expr* iff = nullptr;
};

// A.2.11 cover_point: `[ [ data_type_or_implicit ] label : ] coverpoint
// expression [ iff ( expression ) ] bins_or_empty` (§19.5).
struct CoverPointDecl {
  SourceLoc loc;
  bool has_data_type = false;
  DataType data_type;
  std::string_view label;
  Expr* expr = nullptr;
  Expr* iff = nullptr;
  std::vector<BinsOrOptions> bins;
};

// The alternatives of A.2.11's select_expression and select_condition
// (§19.6.1, §19.6.1.1, §19.6.1.2, §19.6.1.4).
enum class SelectExpressionKind : uint8_t {
  // `binsof ( bins_expression ) [ intersect { covergroup_range_list } ]`.
  kBinsOf,
  kNot,
  kAnd,
  kOr,
  kParenthesized,
  // `select_expression with ( ... ) [ matches ... ]`.
  kWith,
  kCrossIdentifier,
  // `cross_set_expression [ matches ... ]`.
  kCrossSet,
};

struct SelectExpression {
  SelectExpressionKind kind = SelectExpressionKind::kBinsOf;
  SourceLoc loc;
  // kBinsOf: A.2.11's bins_expression, `variable` or `cover_point [ . bin ]`.
  std::string_view bins_of;
  std::string_view bins_of_bin;
  std::vector<CovergroupValueRange> intersect;
  // kNot, kParenthesized and kWith: the operand; kAnd and kOr: both.
  SelectExpression* lhs = nullptr;
  SelectExpression* rhs = nullptr;
  // kWith: the with_covergroup_expression; kCrossSet: the
  // cross_set_expression.
  Expr* expr = nullptr;
  // kWith and kCrossSet: the integer_covergroup_expression after `matches`,
  // null where none is written; matches_dollar for `matches $`.
  Expr* matches = nullptr;
  bool matches_dollar = false;
  // kCrossIdentifier: the cross named.
  std::string_view cross_name;
};

// A.2.11 bins_selection: `bins_keyword name = select_expression [ iff (
// expression ) ]` (§19.6.1).
struct BinsSelection {
  SourceLoc loc;
  BinsKeyword keyword = BinsKeyword::kBins;
  std::string_view name;
  SelectExpression* select = nullptr;
  Expr* iff = nullptr;
};

// A.2.11 cross_body_item: a function_declaration, or a
// bins_selection_or_option.
enum class CrossBodyItemKind : uint8_t { kFunction, kOption, kBinsSelection };

struct CrossBodyItem {
  CrossBodyItemKind kind = CrossBodyItemKind::kBinsSelection;
  ModuleItem* function = nullptr;
  CoverageOption option;
  BinsSelection bins;
};

// A.2.11 cross_item: a cover_point_identifier or variable_identifier.
struct CrossItem {
  std::string_view name;
  SourceLoc loc;
};

// A.2.11 cover_cross: `[ label : ] cross list_of_cross_items [ iff (
// expression ) ] cross_body` (§19.6).
struct CoverCrossDecl {
  SourceLoc loc;
  std::string_view label;
  std::vector<CrossItem> items;
  Expr* iff = nullptr;
  std::vector<CrossBodyItem> body;
};

// A.2.11 coverage_spec_or_option.
enum class CoverageSpecKind : uint8_t { kCoverPoint, kCoverCross, kOption };

struct CoverageSpecOrOption {
  CoverageSpecKind kind = CoverageSpecKind::kCoverPoint;
  CoverPointDecl* cover_point = nullptr;
  CoverCrossDecl* cover_cross = nullptr;
  CoverageOption option;
};

// The alternative of A.2.11's coverage_event a covergroup takes (§19.3,
// §19.8.1).
enum class CoverageEventKind : uint8_t {
  kNone,
  kClocking,
  kSampleFunction,
  kBlockEvent,
};

// A.2.11 block_event_expression: `begin` or `end` of a named block, task,
// function or method, joined by `or` (§19.3).
struct BlockEventTerm {
  bool is_begin = true;
  std::vector<std::string_view> path;
};

struct CoverageEvent {
  CoverageEventKind kind = CoverageEventKind::kNone;
  // kClocking: the events of A.6.5's clocking_event.
  std::vector<EventExpr> clocking;
  // kSampleFunction: the formals of `with function sample ( ... )`.
  std::vector<FunctionArg> sample_formals;
  // kBlockEvent: the terms of the block_event_expression.
  std::vector<BlockEventTerm> block_event;
};

// A.2.11 covergroup_declaration (§19.3, §19.4.1).
struct CovergroupDecl {
  std::string_view name;
  // `covergroup extends base ;`: the base covergroup; empty otherwise.
  std::string_view extends_base;
  std::vector<FunctionArg> formals;
  CoverageEvent event;
  std::vector<CoverageSpecOrOption> items;
};

}  // namespace delta
