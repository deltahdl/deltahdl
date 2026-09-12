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
  // A.7.1: the list_of_path_outputs of a pulsestyle_declaration or a
  // showcancelled_declaration, each entry A.7.3's
  // specify_output_terminal_descriptor as a path's destination is.
  std::vector<SpecifyTerminal> path_outputs;

  std::string_view param_name;
  Expr* param_value = nullptr;
  // A.2.1.1: `specparam_declaration ::= specparam [ packed_dimension ]
  // list_of_specparam_assignments ;`. The range is written once and governs
  // every assignment of the declaration, so each item made from one carries it.
  Expr* param_packed_left = nullptr;
  Expr* param_packed_right = nullptr;

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
  // The one bit the output holds when simulation begins, where the parser can
  // read it: §29.3.3's initial statement assigns one of A.5.3's init_val
  // literals, and A.5.2's `output reg port_identifier = constant_expression`
  // may write a literal too. 'x' where nothing gave one, and where the header
  // wrote an expression the parser cannot fold, which the run evaluates from
  // initial_expr instead.
  char initial_value = 'x';
  // A.5.2's constant_expression as written after `output reg port_identifier
  // =`, kept for the run to evaluate: `~1'b0` is the negation of a literal and
  // not the literal, so the bit it stands for is not one the parser can read.
  // Null where the initial value came from §29.3.3's initial statement, whose
  // right-hand side A.5.3 closes over literals, or where there is none.
  Expr* initial_expr = nullptr;
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
