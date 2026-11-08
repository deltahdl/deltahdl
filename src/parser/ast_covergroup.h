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

struct CoverageOption {
  bool is_type_option = false;
  std::string_view member;
  SourceLoc loc;
  Expr* value = nullptr;
};

enum class CovergroupValueRangeKind : uint8_t {
  kValue,
  kRange,
  kAbsoluteTolerance,
  kRelativeTolerance,
};

struct CovergroupValueRange {
  CovergroupValueRangeKind kind = CovergroupValueRangeKind::kValue;
  Expr* lo = nullptr;
  Expr* hi = nullptr;
};

enum class TransRepetition : uint8_t {
  kNone,
  kConsecutive,
  kGoto,
  kNonconsecutive,
};

struct TransRangeList {
  std::vector<CovergroupValueRange> items;
  TransRepetition repetition = TransRepetition::kNone;
  Expr* repeat_lo = nullptr;
  Expr* repeat_hi = nullptr;
};

struct TransSet {
  SourceLoc loc;
  std::vector<TransRangeList> steps;
};

enum class BinsKeyword : uint8_t { kBins, kIllegalBins, kIgnoreBins };

enum class BinsOrOptionsKind : uint8_t {
  kOption,
  kValues,
  kCoverPointWith,
  kSetExpression,
  kTransitions,
  kDefault,
  kDefaultSequence,
};

struct BinsOrOptions {
  BinsOrOptionsKind kind = BinsOrOptionsKind::kValues;
  SourceLoc loc;
  CoverageOption option;
  bool wildcard = false;
  BinsKeyword keyword = BinsKeyword::kBins;
  std::string_view name;
  bool is_array = false;
  Expr* array_size = nullptr;
  std::vector<CovergroupValueRange> ranges;
  std::string_view with_cover_point;
  Expr* with_expr = nullptr;
  Expr* set_expr = nullptr;
  std::vector<TransSet> transitions;
  Expr* iff = nullptr;
};

struct CoverPointDecl {
  SourceLoc loc;
  bool has_data_type = false;
  DataType data_type;
  std::string_view label;
  Expr* expr = nullptr;
  Expr* iff = nullptr;
  std::vector<BinsOrOptions> bins;
};

enum class SelectExpressionKind : uint8_t {
  kBinsOf,
  kNot,
  kAnd,
  kOr,
  kParenthesized,
  kWith,
  kCrossIdentifier,
  kCrossSet,
};

struct SelectExpression {
  SelectExpressionKind kind = SelectExpressionKind::kBinsOf;
  SourceLoc loc;
  std::string_view bins_of;
  std::string_view bins_of_bin;
  std::vector<CovergroupValueRange> intersect;
  SelectExpression* lhs = nullptr;
  SelectExpression* rhs = nullptr;
  Expr* expr = nullptr;
  Expr* matches = nullptr;
  bool matches_dollar = false;
  std::string_view cross_name;
};

struct BinsSelection {
  SourceLoc loc;
  BinsKeyword keyword = BinsKeyword::kBins;
  std::string_view name;
  SelectExpression* select = nullptr;
  Expr* iff = nullptr;
};

enum class CrossBodyItemKind : uint8_t { kFunction, kOption, kBinsSelection };

struct CrossBodyItem {
  CrossBodyItemKind kind = CrossBodyItemKind::kBinsSelection;
  ModuleItem* function = nullptr;
  CoverageOption option;
  BinsSelection bins;
};

struct CrossItem {
  std::string_view name;
  SourceLoc loc;
};

struct CoverCrossDecl {
  SourceLoc loc;
  std::string_view label;
  std::vector<CrossItem> items;
  Expr* iff = nullptr;
  std::vector<CrossBodyItem> body;
};

enum class CoverageSpecKind : uint8_t { kCoverPoint, kCoverCross, kOption };

struct CoverageSpecOrOption {
  CoverageSpecKind kind = CoverageSpecKind::kCoverPoint;
  CoverPointDecl* cover_point = nullptr;
  CoverCrossDecl* cover_cross = nullptr;
  CoverageOption option;
};

enum class CoverageEventKind : uint8_t {
  kNone,
  kClocking,
  kSampleFunction,
  kBlockEvent,
};

struct BlockEventTerm {
  bool is_begin = true;
  std::vector<std::string_view> path;
};

struct CoverageEvent {
  CoverageEventKind kind = CoverageEventKind::kNone;
  std::vector<EventExpr> clocking;
  std::vector<FunctionArg> sample_formals;
  std::vector<BlockEventTerm> block_event;
};

struct CovergroupDecl {
  std::string_view name;
  std::string_view extends_base;
  std::vector<FunctionArg> formals;
  CoverageEvent event;
  std::vector<CoverageSpecOrOption> items;
};

}  // namespace delta
