#pragma once

#include <array>
#include <cstdint>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "parser/ast_design.h"
#include "parser/ast_module.h"
#include "parser/ast_specify.h"
#include "parser/ast_type.h"

namespace delta {

struct SpecparamValue {
  std::string name;
  uint64_t value = 0;
  double real_value = 0.0;
};

struct InterconnectDelay {
  std::string src_port;
  std::string dst_port;
  uint64_t rise = 0;
  uint64_t fall = 0;
  uint64_t delays[12] = {};
  uint64_t reject_limit[12] = {};
  uint64_t error_limit[12] = {};

  std::vector<std::string> covered_sources;
};

enum class SdfInterconnectConstruct : uint8_t {
  kInterconnect,
  kPort,
  kNetdelay,
};

struct InterconnectTerminal {
  std::string name;
  std::string net;
  Direction direction = Direction::kNone;
  bool is_primitive_pin = false;
};

struct InterconnectNet {
  std::string name;
  std::string id;
};

struct InterconnectTopology {
  std::vector<InterconnectTerminal> terminals;
  std::vector<InterconnectNet> nets;
  std::vector<std::string> primitive_instances;
};

InterconnectTopology CollectInterconnectTopology(const CompilationUnit& cu,
                                                 const ModuleDecl& top);

struct PathDelayRetention {
  std::array<bool, 12> delay{};
  std::array<bool, 12> reject{};
  std::array<bool, 12> error{};

  static PathDelayRetention PulseLimits(bool reject_held, bool error_held) {
    PathDelayRetention retain;
    retain.reject.fill(reject_held);
    retain.error.fill(error_held);
    return retain;
  }
};

struct SdfInterconnectAnnotation {
  std::string source;
  std::string load;
  SdfInterconnectConstruct construct = SdfInterconnectConstruct::kInterconnect;
  uint64_t delays[12] = {};
  bool is_increment = false;
  PathDelayRetention held;
  bool limits_written = false;
  uint64_t reject_limit[12] = {};
  uint64_t error_limit[12] = {};
};

struct SdfInterconnectOutcome {
  bool annotated = false;
  std::vector<std::string> warnings;
};

struct InterconnectReferenceRead {
  bool delayed = false;
  uint64_t delay = 0;
  std::string load_port;
};

struct SdfTcAnnotation {
  TimingCheckKind kind = TimingCheckKind::kSetup;
  std::string ref_signal;
  SpecifyEdge ref_edge = SpecifyEdge::kNone;
  std::string data_signal;
  SpecifyEdge data_edge = SpecifyEdge::kNone;
  std::string ref_select;
  std::string data_select;
  std::vector<std::pair<char, char>> ref_edge_descriptors;
  std::vector<std::pair<char, char>> data_edge_descriptors;
  std::string ref_condition;
  std::string data_condition;
  std::string condition;
  int64_t limit = 0;
  int64_t limit2 = 0;
  int64_t start_edge_offset = 0;
  int64_t end_edge_offset = 0;
  bool set_limit = false;
  bool set_limit2 = false;
  bool set_start_edge_offset = false;
  bool set_end_edge_offset = false;
};

struct PulseControlSpecparam {
  std::string_view input;
  std::string_view output;
  std::string_view inst_prefix;
  uint64_t reject = 0;
  bool has_error = false;
  uint64_t error = 0;
};

struct SdfPulseLimitSpec {
  std::string_view src;
  std::string_view dst;
  int64_t reject = 0;
  int64_t error = 0;
  bool has_error = false;
  bool is_percent = false;
  bool is_increment = false;
};

struct SdfDeviceAnnotation {
  std::string_view port_instance;
  uint64_t delays[12] = {};
  uint64_t three_state_delays[4] = {};
  bool is_increment = false;
  std::array<bool, 12> held{};
  std::array<bool, 4> three_state_held{};
};

using SdfPathDelayIncrement = std::array<int64_t, 12>;

struct SdfPulseLimitIncrement {
  SdfPathDelayIncrement reject{};
  SdfPathDelayIncrement error{};
};

}  // namespace delta
