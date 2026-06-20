#pragma once

#include <cstdint>
#include <string_view>
#include <utility>
#include <vector>

#include "common/source_loc.h"
#include "parser/ast_expr.h"

namespace delta {

enum class SpecifyPathKind : uint8_t {
  kParallel,
  kFull,
};

enum class SpecifyEdge : uint8_t {
  kNone,
  kPosedge,
  kNegedge,
  kEdge,
};

enum class SpecifyPolarity : uint8_t {
  kNone,
  kPositive,
  kNegative,
};

enum class SpecifyRangeKind : uint8_t {
  kNone,
  kBitSelect,
  kPartSelect,
  kPlusIndexed,
  kMinusIndexed,
};

struct SpecifyTerminal {
  std::string_view name;
  std::string_view interface_name;
  Expr* range_left = nullptr;
  Expr* range_right = nullptr;
  SpecifyRangeKind range_kind = SpecifyRangeKind::kNone;
};

struct SpecifyPathDecl {
  SpecifyPathKind path_kind = SpecifyPathKind::kParallel;
  SpecifyEdge edge = SpecifyEdge::kNone;
  SpecifyPolarity polarity = SpecifyPolarity::kNone;
  SpecifyPolarity dst_polarity = SpecifyPolarity::kNone;
  std::vector<SpecifyTerminal> src_ports;
  std::vector<SpecifyTerminal> dst_ports;
  std::vector<Expr*> delays;
  Expr* condition = nullptr;
  Expr* data_source = nullptr;
  bool is_ifnone = false;
  SourceLoc loc;
};

enum class TimingCheckKind : uint8_t {
  kSetup,
  kHold,
  kSetuphold,
  kRecovery,
  kRemoval,
  kRecrem,
  kWidth,
  kPeriod,
  kSkew,
  kNochange,
  kTimeskew,
  kFullskew,
};

struct TimingCheckDecl {
  TimingCheckKind check_kind = TimingCheckKind::kSetup;
  SpecifyEdge ref_edge = SpecifyEdge::kNone;
  SpecifyTerminal ref_terminal;
  Expr* ref_condition = nullptr;
  std::vector<std::pair<char, char>> ref_edge_descriptors;
  SpecifyEdge data_edge = SpecifyEdge::kNone;
  SpecifyTerminal data_terminal;
  Expr* data_condition = nullptr;
  std::vector<std::pair<char, char>> data_edge_descriptors;
  std::vector<Expr*> limits;
  std::string_view notifier;

  Expr* timestamp_cond = nullptr;
  Expr* timecheck_cond = nullptr;
  std::string_view delayed_ref;
  Expr* delayed_ref_expr = nullptr;
  std::string_view delayed_data;
  Expr* delayed_data_expr = nullptr;

  Expr* event_based_flag = nullptr;
  Expr* remain_active_flag = nullptr;
  SourceLoc loc;
};

enum class SpecifyItemKind : uint8_t {
  kPathDecl,
  kTimingCheck,
  kPulsestyle,
  kShowcancelled,
  kSpecparam,
};

struct SpecifyItem {
  SpecifyItemKind kind = SpecifyItemKind::kPathDecl;
  SourceLoc loc;

  SpecifyPathDecl path;

  TimingCheckDecl timing_check;

  bool is_ondetect = false;
  bool is_noshowcancelled = false;
  std::vector<std::string_view> signal_list;

  std::string_view param_name;
  Expr* param_value = nullptr;

  bool is_pathpulse = false;
  std::string_view pathpulse_input;
  std::string_view pathpulse_output;
  Expr* pathpulse_reject = nullptr;
  Expr* pathpulse_error = nullptr;
};

struct UdpTableRow {
  std::vector<char> inputs;

  std::vector<std::pair<char, char>> paren_edges;
  char current_state = 0;
  char output = '0';
};

struct UdpDecl {
  std::string_view name;
  SourceRange range;
  std::vector<Attribute> attrs;
  std::string_view output_name;
  std::vector<std::string_view> input_names;
  bool is_sequential = false;
  bool has_initial = false;
  char initial_value = 'x';
  std::vector<UdpTableRow> table;
  std::string_view library;
};

struct LibraryDecl {
  std::string_view name;
  std::vector<std::string_view> file_paths;
  std::vector<std::string_view> incdir_paths;
  SourceRange range;
};

struct IncludeStmt {
  std::string_view file_path;
  SourceLoc loc;
};

}  // namespace delta
