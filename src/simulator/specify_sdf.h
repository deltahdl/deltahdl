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
  // The value exactly as written, a fraction included, which a specparam of
  // type real (§6.20.5) takes in place of `value`, the number rounded.
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

  // §32.4.4: the sources this delay is the delay from. Empty stands for every
  // source on the net, which is what a PORT or a NETDELAY entry supplies and
  // what an INTERCONNECT entry falls back to on a multisource net whose named
  // source could not be placed. A source given as a name higher in the
  // hierarchy than the load contributes every source at or above it, since a
  // delay from a source port is a delay from all of that port's sources.
  std::vector<std::string> covered_sources;
};

// §32.4.4 Table 32-3: the construct an interconnect delay arrived under. All
// three rows annotate the same structure, but each names its target its own
// way, so the rule for finding what to annotate differs per row.
enum class SdfInterconnectConstruct : uint8_t {
  kInterconnect,
  kPort,
  kNetdelay,
};

// §32.4.4: one terminal an SDF interconnect entry can name -- a port of a
// module instance or a pin of a gate primitive. `net` is the identity of the
// net the terminal attaches to; two terminals carrying the same net identity
// are connected, including across a hierarchy boundary, since a port connection
// joins the parent's net and the instance's own port net into one net.
struct InterconnectTerminal {
  std::string name;
  std::string net;
  Direction direction = Direction::kNone;
  bool is_primitive_pin = false;
};

// §32.4.4: one net of the design. `name` is how the design spells it and `id`
// is the identity it shares with every net a port connection joins it to, so
// two names that are really one net carry one id.
struct InterconnectNet {
  std::string name;
  std::string id;
};

// §32.4.4: the design-side connectivity interconnect annotation is matched
// against. An interconnect delay has no SystemVerilog declaration behind it, so
// what an entry names has to be looked up in the design's own hierarchy of
// ports, nets and primitives instead.
struct InterconnectTopology {
  std::vector<InterconnectTerminal> terminals;
  std::vector<InterconnectNet> nets;
  std::vector<std::string> primitive_instances;
};

// §32.4.4: walk an elaborated module hierarchy and record what an SDF
// interconnect entry may name: every module-instance port with its direction
// and the net it sits on, every net, and every gate primitive (whose pins an
// interconnect delay may never be annotated between). Hierarchical names are
// written the way an SDF file writes them, with `/` between levels.
InterconnectTopology CollectInterconnectTopology(const CompilationUnit& cu,
                                                 const ModuleDecl& top);

// §32.5: which of a module path's twelve delays and twelve pairs of pulse
// limits an annotation holds at the value the path already carries instead of
// overwriting it. An IOPATH may write any delay or limit as an empty pair of
// parentheses, which holds what it stands for, and §32.8's Table 32-4 spreads
// what it wrote over the transitions slot by slot, so each slot is held or
// written on its own.
struct PathDelayRetention {
  std::array<bool, 12> delay{};
  std::array<bool, 12> reject{};
  std::array<bool, 12> error{};

  // Every slot of the reject limit, of the error limit, or of both, held.
  static PathDelayRetention PulseLimits(bool reject_held, bool error_held) {
    PathDelayRetention retain;
    retain.reject.fill(reject_held);
    retain.error.fill(error_held);
    return retain;
  }
};

// §32.4.4: one SDF interconnect entry ready to be applied. `source` is empty
// for the PORT and NETDELAY rows, which carry only a load and delay values;
// `load` is a load port for the INTERCONNECT and PORT rows and may also be a
// net for the NETDELAY row.
struct SdfInterconnectAnnotation {
  std::string source;
  std::string load;
  SdfInterconnectConstruct construct = SdfInterconnectConstruct::kInterconnect;
  uint64_t delays[12] = {};
  bool is_increment = false;
  // §32.5: the transitions whose delay or limits the entry left as they stood,
  // written as empty parentheses or left out of a min:typ:max triple.
  PathDelayRetention held;
  // Where the entry wrote its values with their pulse limits, `((d) (r) (e))`,
  // the limits it stated; otherwise the limits come from the percentages.
  bool limits_written = false;
  uint64_t reject_limit[12] = {};
  uint64_t error_limit[12] = {};
};

// §32.4.4: what became of one interconnect entry -- whether it reached anything
// at all, and every complaint the annotator has about it. An entry can both
// warn and annotate: an INTERCONNECT whose source cannot be placed on the
// load's net is warned about and its delay applied to the load anyway.
struct SdfInterconnectOutcome {
  bool annotated = false;
  std::vector<std::string> warnings;
};

// §32.4.4: which of the two values a reference to a signal reads. A reference
// at or hierarchically after an annotated load reads the delayed value and
// therefore carries that load's delay; every reference before it, the source
// among them, reads the undelayed value.
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
  // §32.4.2: the select each signal was written with, `[0]` or `[3:2]`, as the
  // file spelled it; empty where it carries none.
  std::string ref_select;
  std::string data_select;
  // §32.4.2: the descriptor an SDF transition edge stands for, where the edge
  // is SpecifyEdge::kEdge.
  std::vector<std::pair<char, char>> ref_edge_descriptors;
  std::vector<std::pair<char, char>> data_edge_descriptors;
  // §32.4.2: the condition each signal was written with, matched against the
  // declared check's condition on that same signal.
  std::string ref_condition;
  std::string data_condition;
  std::string condition;
  // Signed, since §31.9 gives a $setuphold's or a $recrem's limits a meaning
  // below zero; every other limit takes a negative value as 0.
  int64_t limit = 0;
  int64_t limit2 = 0;
  int64_t start_edge_offset = 0;
  int64_t end_edge_offset = 0;
  bool set_limit = false;
  bool set_limit2 = false;
  bool set_start_edge_offset = false;
  bool set_end_edge_offset = false;
};

// §30.7.1: a PATHPULSE$ pulse-control specparam gathered from a specify block.
// `input`/`output` name the module path terminals; when both are empty the
// specparam is not path-specific and applies to every module path in the
// module. `reject` is the reject limit and, when `has_error` is set, `error` is
// the separately given error limit; otherwise the reject limit also serves as
// the error limit.
struct PulseControlSpecparam {
  std::string_view input;
  std::string_view output;
  // The hierarchical prefix of the module instance whose specify block declared
  // this PATHPULSE$ specparam, ending in a `.` and empty for a module
  // elaborated as a top. §30.7.1 has a specparam naming no module path cover
  // every module path the module defines, so it narrows the paths of
  // the instance that declared it and no others; this is what matches it
  // against PathDelay::inst_prefix in simulator/specify_path_delay.h.
  std::string_view inst_prefix;
  uint64_t reject = 0;
  bool has_error = false;
  uint64_t error = 0;
};

// An SDF PATHPULSE pulse-limit specification applied to the module path that
// runs from src to dst. reject/error are the reject and error pulse limits;
// when has_error is false the reject limit also serves as the error limit. When
// is_percent is set the limits are percentages of the path delay rather than
// absolute time values.
//
// §32.7: with is_increment set, the two values are amounts to change the limits
// the path already holds by rather than the limits themselves, and an amount
// may be negative to lower a limit -- which is why they are signed. A
// percentage amount is still a fraction of the path's delay, so it is the
// change that is worked out from the delay rather than the limit itself.
struct SdfPulseLimitSpec {
  std::string_view src;
  std::string_view dst;
  int64_t reject = 0;
  int64_t error = 0;
  bool has_error = false;
  bool is_percent = false;
  bool is_increment = false;
};

// §32.4.1 Table 32-1: an SDF DEVICE delay ready to be applied. `port_instance`
// is the entry's optional operand; when it is empty the delay reaches every
// module output. `is_increment` selects whether the values replace what is
// already there or add to it.
//
// §32.8: the entry's values reach a construct that carries twelve state
// transition delays -- a specify path -- or one that carries three, such as a
// gate primitive, and which of the two is not known until the targets are
// found. Both mappings of the one value list are therefore carried here.
// `delays` holds the Table 32-4 expansion over the twelve transitions, and
// `three_state_delays` the same list mapped for a three-delay construct: its
// first three entries are the values the entry listed, any beyond the third
// dropped, and its fourth the delay to the x state, the smallest of those
// three.
struct SdfDeviceAnnotation {
  std::string_view port_instance;
  uint64_t delays[12] = {};
  uint64_t three_state_delays[4] = {};
  bool is_increment = false;
  // §32.5: the transitions of a path, and the three delays and the delay to x
  // of a primitive, the entry left as they stood.
  std::array<bool, 12> held{};
  std::array<bool, 4> three_state_held{};
};

// §32.7 (printed pages 930-931): what an INCREMENT entry adds to a module path,
// one amount per transition of §32.8 Table 32-4. Signed, since a negative value
// in INCREMENT mode lowers the delay it is added to.
using SdfPathDelayIncrement = std::array<int64_t, 12>;

// §32.7: what an INCREMENT entry adds to a module path's reject and error
// limits, one amount per transition of each.
struct SdfPulseLimitIncrement {
  SdfPathDelayIncrement reject{};
  SdfPathDelayIncrement error{};
};

}  // namespace delta
