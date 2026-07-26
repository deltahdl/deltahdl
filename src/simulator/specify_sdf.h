#pragma once

#include <cstdint>
#include <functional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

#include "common/types.h"
#include "parser/ast.h"
#include "simulator/specify_timing_check.h"

namespace delta {

struct SdfAnnotation {
  std::string sdf_file;
  std::string scope;
};

struct SpecparamValue {
  std::string name;
  uint64_t value = 0;
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
};

// §32.4.4: what became of one interconnect entry -- whether it reached anything
// at all, and every complaint the annotator has about it. An entry can both
// warn and annotate: an INTERCONNECT whose source cannot be placed on the
// load's net is warned about and its delay applied to the load anyway.
struct SdfInterconnectOutcome {
  bool annotated = false;
  std::vector<std::string> warnings;
};

// §32.4.4: one source-side transition arriving at an annotated load, the
// interconnect delay later than the source took the value. This is what makes a
// reference at or after the load read the delayed signal value while a
// reference to the source keeps reading the undelayed one.
struct InterconnectArrival {
  std::string load_port;
  uint64_t value = 0;
  uint64_t time = 0;
  uint64_t delay = 0;
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
  std::string condition;
  uint64_t limit = 0;
  uint64_t limit2 = 0;
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
  uint64_t reject = 0;
  bool has_error = false;
  uint64_t error = 0;
};

// An SDF PATHPULSE pulse-limit specification applied to the module path that
// runs from src to dst. reject/error are the reject and error pulse limits;
// when has_error is false the reject limit also serves as the error limit. When
// is_percent is set the limits are percentages of the path delay rather than
// absolute time values.
struct SdfPulseLimitSpec {
  std::string_view src;
  std::string_view dst;
  uint64_t reject = 0;
  uint64_t error = 0;
  bool has_error = false;
  bool is_percent = false;
};

// §32.4.1 Table 32-1: an SDF DEVICE delay ready to be applied. `port_instance`
// is the entry's optional operand; when it is empty the delay reaches every
// module output. `delays` holds the twelve transition values the entry
// supplied, and `is_increment` selects whether they replace what is already
// there or add to it.
struct SdfDeviceAnnotation {
  std::string_view port_instance;
  uint64_t delays[12] = {};
  bool is_increment = false;
};

// §32.5: which of a module path's two pulse limits an annotation holds at the
// value the path already carries instead of overwriting it. The extended IOPATH
// form writes each limit either as a value or as an empty pair of parentheses,
// and an empty one asks for that limit to be held -- independently of the
// other, so an entry may supply one limit and hold the other.
struct PathDelayPulseRetention {
  bool reject = false;
  bool error = false;
};

}  // namespace delta
