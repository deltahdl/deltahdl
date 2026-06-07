#pragma once

#include <cstdint>
#include <fstream>
#include <string>
#include <string_view>
#include <vector>

#include "common/types.h"

namespace delta {

struct Variable;

// §21.7.5 (Table 21-11): SystemVerilog does not extend the IEEE Std 1364-2005
// VCD format, so a SystemVerilog data type is dumped by masquerading as a
// 1364-2005 type. This selects which type the dumped object maps to. kNet keeps
// the net mapping of §21.7.2.3 (wire) and is the default so nets and the 4-state
// objects of the earlier subclauses keep their existing declaration form.
enum class VcdDataType : uint8_t {
  kNet,       // a net: var_type wire (§21.7.2.3)
  kBit,       // -> reg, size = total packed dimension
  kLogic,     // -> reg, size = total packed dimension
  kInt,       // -> integer, size 32
  kShortint,  // -> reg, size 16
  kLongint,   // -> reg, size 64
  kByte,      // -> reg, size 8
  kEnum,      // -> integer, size 32 (default for an untyped enum)
  kReal,      // -> real (also shortreal)
};

// §21.7.5: an unpacked structure is dumped as a named fork-join block so it is
// easy to tell apart from a begin-end block; every other scope is a module.
enum class VcdScopeKind : uint8_t {
  kModule,
  kFork,
};

struct VcdSignal {
  std::string_view name;
  uint32_t width = 1;
  Variable* var = nullptr;
  char ident = '!';
  // Net type of the dumped object, used to pick the $var var_type keyword
  // (§21.7.2.3): a uwire net is recorded as wire.
  NetType net_type = NetType::kWire;
  // §21.7.5 (Table 21-11): the SystemVerilog data type of the dumped object,
  // used to pick the 1364-2005 var_type keyword and the size it masquerades as.
  VcdDataType data_type = VcdDataType::kNet;
  // Extended VCD node information (§21.7.4.2): the declared index range of a
  // port and the integer identifier code used in its $var declaration. msb/lsb
  // are negative when no vector_index applies, in which case the port is a
  // 1-bit scalar.
  int32_t msb = -1;
  int32_t lsb = -1;
  uint32_t port_id = 0;
};

class VcdWriter {
 public:
  explicit VcdWriter(const std::string& filename);
  ~VcdWriter();

  VcdWriter(const VcdWriter&) = delete;
  VcdWriter& operator=(const VcdWriter&) = delete;

  bool IsOpen() const { return ofs_.is_open(); }

  // Emit the VCD header (§21.7.2.3 keyword sections). When the $dumpfile
  // filename was given by a variable or expression, dumpfile_literal carries
  // that unevaluated literal so it can be reproduced in the $version section.
  void WriteHeader(std::string_view timescale,
                   std::string_view dumpfile_literal = {});
  // §21.7.5: kModule emits a $scope module section; an unpacked structure is
  // dumped as a named fork-join block, emitting a $scope fork section instead.
  void BeginScope(std::string_view name,
                  VcdScopeKind kind = VcdScopeKind::kModule);
  void EndScope();
  void RegisterSignal(std::string_view name, uint32_t width, Variable* var,
                      NetType net_type = NetType::kWire, int32_t msb = -1,
                      int32_t lsb = -1,
                      VcdDataType data_type = VcdDataType::kNet);
  void EndDefinitions();

  void WriteTimestamp(uint64_t time);
  void DumpAllValues();
  void DumpSelectedValues(const std::vector<std::string_view>& names);
  void DumpChangedValues(uint64_t prev_time);

  // Generate a checkpoint (§21.7.1.4): emit a $dumpall checkpoint recording the
  // current value of every selected variable.
  void DumpAll();

  // Suspend the dump (§21.7.1.3): emit a checkpoint that records every selected
  // variable as x and then stop recording further value changes.
  void DumpOff();
  // Resume the dump (§21.7.1.3): re-enable recording and emit a checkpoint of
  // each variable's current value.
  void DumpOn();

  void SetEnabled(bool enabled) { enabled_ = enabled; }
  bool IsEnabled() const { return enabled_; }

  // Read the dump file during simulation (§21.7.1.6): push any buffered output
  // out to the file so an application reading the file mid-simulation sees every
  // value change recorded so far. The dump state is untouched, so dumping
  // continues afterward exactly as before and no value changes are lost.
  void Flush();

  // Limit the dump file size (§21.7.1.5): once the file reaches limit_bytes the
  // dumper stops recording and inserts a comment noting the limit was reached.
  void SetSizeLimit(uint64_t limit_bytes) { size_limit_ = limit_bytes; }

  // Mark this writer as producing an extended VCD file (§21.7.3). The extended
  // VCD format adds the $vcdclose keyword command over the 4-state format, so
  // only an extended writer emits it.
  void SetExtended() { extended_ = true; }

  // Emit the node information section in the extended VCD form (§21.7.4.2). The
  // $dumpports task records ports rather than the 4-state nets/variables, so
  // each $var declaration uses the var_type keyword port, prints the port's
  // declared index range (or 1 for a scalar) as its size, and identifies the
  // port with an integer code preceded by < that ascends from zero in
  // declaration order. This is independent of the 4-state declaration form used
  // by a plain writer.
  void SetExtendedPortNodes() { port_nodes_ = true; }

  // Emit the $vcdclose keyword command (§21.7.3.6.1): when an extended VCD file
  // is closed, record the final simulation time so a reader knows the end time
  // regardless of whether any signal changed at that time. Syntax 21-26:
  // $vcdclose <final_simulation_time> $end. A 4-state writer emits nothing.
  void WriteVcdClose(uint64_t final_time);

 private:
  void WriteScalarChange(const VcdSignal& sig);
  void WriteVectorChange(const VcdSignal& sig);
  // Emit a real value change (§21.7.2.1): real variables are dumped as real
  // numbers using a %.16g format so all 53 mantissa bits are preserved.
  void WriteRealChange(const VcdSignal& sig);
  // Emit a port value change in the extended VCD form (§21.7.4.3, Syntax 21-29):
  // the key character p, the port_value state character(s), the strength0 and
  // strength1 strength components, then the port's identifier code (< followed by
  // its integer code as written in the $var declaration).
  void WritePortValueChange(const VcdSignal& sig);
  void WriteSignalChange(const VcdSignal& sig);
  void WriteSignalAllX(const VcdSignal& sig);
  // Returns true once the configured size limit has been reached, emitting the
  // limit comment exactly once when the threshold is first crossed.
  bool AtSizeLimit();

  std::ofstream ofs_;
  std::vector<VcdSignal> signals_;
  char next_ident_ = '!';
  bool enabled_ = true;
  uint64_t last_time_ = 0;
  bool header_written_ = false;
  uint64_t size_limit_ = 0;
  bool limit_reached_ = false;
  bool extended_ = false;
  bool port_nodes_ = false;
  uint32_t next_port_id_ = 0;
};

}
