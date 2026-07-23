#include "simulator/vcd_writer.h"

#include <cstdio>
#include <cstring>
#include <ctime>

#include "simulator/variable.h"

namespace delta {

// §21.7.2.3: the $date section indicates the date on which the VCD file was
// generated, so the header stamps the host clock at header-writing time.
static std::string CurrentDateText() {
  std::time_t now = std::time(nullptr);
  std::tm tm_buf{};
  localtime_r(&now, &tm_buf);
  char buf[64];
  std::strftime(buf, sizeof(buf), "%b %d, %Y %H:%M:%S", &tm_buf);
  return buf;
}

VcdWriter::VcdWriter(const std::string& filename) : ofs_(filename) {}

VcdWriter::~VcdWriter() {
  if (ofs_.is_open()) ofs_.close();
}

void VcdWriter::WriteHeader(std::string_view timescale,
                            std::string_view dumpfile_literal) {
  if (!ofs_.is_open()) return;
  ofs_ << "$date\n  " << CurrentDateText() << "\n$end\n";
  // §21.7.2.3: the $version section names the VCD writer and the $dumpfile call
  // that created the file. When the filename was supplied by a variable or an
  // expression, the unevaluated literal is reproduced here rather than the
  // resolved name.
  ofs_ << "$version\n  DeltaHDL 0.1.0\n";
  if (!dumpfile_literal.empty()) {
    ofs_ << "  $dumpfile(" << dumpfile_literal << ")\n";
  }
  ofs_ << "$end\n";
  ofs_ << "$timescale\n  " << timescale << "\n$end\n";
  header_written_ = true;
}

// §21.7.2.3: the scope_type keyword written in a $scope section indicates the
// kind of scope -- module for a top-level module or module instance, task for
// a task, function for a function, begin for a named sequential block, and
// fork for a named parallel block.
static const char* VcdScopeKeyword(VcdScopeKind kind) {
  switch (kind) {
    case VcdScopeKind::kTask:
      return "task";
    case VcdScopeKind::kFunction:
      return "function";
    case VcdScopeKind::kBegin:
      return "begin";
    case VcdScopeKind::kFork:
      return "fork";
    case VcdScopeKind::kModule:
      break;
  }
  return "module";
}

void VcdWriter::BeginScope(std::string_view name, VcdScopeKind kind) {
  if (!ofs_.is_open()) return;
  ofs_ << "$scope " << VcdScopeKeyword(kind) << " " << name << " $end\n";
}

void VcdWriter::EndScope() {
  if (!ofs_.is_open()) return;
  ofs_ << "$upscope $end\n";
}

// §21.7.2.3: choose the var_type keyword written in a $var declaration. Real
// variables are dumped as real numbers. A net declared with net type uwire is
// recorded as wire — uwire is not itself a var_type keyword — and this writer
// renders every other binary-valued net as wire as well.
static const char* VcdVarTypeKeyword(const VcdSignal& sig) {
  if (sig.var && sig.var->value.is_real) return "real";
  if (sig.net_type == NetType::kUwire) return "wire";
  return "wire";
}

// §21.7.5 (Table 21-11): map a SystemVerilog data type to the 1364-2005
// var_type keyword and the size it is dumped with. bit and logic keep the full
// packed width passed in (Table 21-11: "total size of packed dimension"), which
// also covers a packed array or structure collapsed to a single reg vector. The
// fixed-width integer types and the default enum carry the size fixed by the
// table regardless of the declared width. A net (kNet) keeps the §21.7.2.3
// keyword and its own width.
static const char* VcdDataTypeKeyword(VcdDataType type) {
  switch (type) {
    case VcdDataType::kBit:
    case VcdDataType::kLogic:
    case VcdDataType::kShortint:
    case VcdDataType::kLongint:
    case VcdDataType::kByte:
      return "reg";
    case VcdDataType::kInt:
    case VcdDataType::kEnum:
      return "integer";
    case VcdDataType::kReal:
      return "real";
    case VcdDataType::kNet:
      break;
  }
  return "wire";
}

static uint32_t VcdDataTypeSize(VcdDataType type, uint32_t width) {
  switch (type) {
    case VcdDataType::kInt:
    case VcdDataType::kEnum:
      return 32;
    case VcdDataType::kShortint:
      return 16;
    case VcdDataType::kLongint:
      return 64;
    case VcdDataType::kByte:
      return 8;
    case VcdDataType::kBit:
    case VcdDataType::kLogic:
    case VcdDataType::kReal:
    case VcdDataType::kNet:
      break;
  }
  return width;
}

// Copy the descriptive registration arguments (everything except the counter
// state) into a fresh VcdSignal. No writer state is consulted or mutated.
static VcdSignal MakeVcdSignalFields(const VcdSignalSpec& spec) {
  VcdSignal sig;
  sig.name = spec.name;
  sig.width = spec.width;
  sig.var = spec.var;
  sig.net_type = spec.net_type;
  sig.data_type = spec.data_type;
  sig.msb = spec.msb;
  sig.lsb = spec.lsb;
  // §21.7.5: where this object's bits sit in its backing variable, and whether
  // it is one member of an unpacked structure sharing that variable.
  sig.bit_offset = spec.bit_offset;
  sig.is_field = spec.is_field;
  return sig;
}

// Assign the per-signal identifier and port codes, advancing the writer's
// counters as §21.7.4.2 requires (the port identifier code ascends one unit
// per registration, in module-declaration order; the printable-ASCII
// identifier wraps back to '!' once it passes '~').
static void AssignVcdSignalCodes(VcdSignal& sig, char& next_ident,
                                 uint32_t& next_port_id) {
  sig.ident = next_ident++;
  // §21.7.4.2: the identifier code of a port is an integer that ascends in
  // one-unit increments for each port, in the order found in the module
  // declaration. Each registration is one such port.
  sig.port_id = next_port_id++;
  if (next_ident > '~') next_ident = '!';
}

// Populate a VcdSignal from the registration arguments, advancing the writer's
// identifier and port counters as §21.7.4.2 requires (the port identifier code
// ascends one unit per registration, in module-declaration order).
static VcdSignal MakeVcdSignal(const VcdSignalSpec& spec, char& next_ident,
                               uint32_t& next_port_id) {
  VcdSignal sig = MakeVcdSignalFields(spec);
  AssignVcdSignalCodes(sig, next_ident, next_port_id);
  return sig;
}

// §21.7.4.2 (Syntax 21-28): $var port <size> <<id> <reference> $end. The
// var_type keyword is always port; the size is the declared index range of a
// bus or 1 for a single-bit port; the identifier code is the integer preceded
// by <. At least one space separates each syntactical element.
static void WritePortVarDecl(std::ofstream& ofs, const VcdSignal& sig,
                             std::string_view name) {
  ofs << "$var port ";
  if (sig.msb >= 0 && sig.lsb >= 0) {
    ofs << "[" << sig.msb << ":" << sig.lsb << "]";
  } else {
    ofs << "1";
  }
  ofs << " <" << sig.port_id << " " << name << " $end\n";
}

// §21.7.5 (Table 21-11): a SystemVerilog data type masquerades as a 1364-2005
// type. A net keeps the §21.7.2.3 mapping (and a real object dumped through
// that path is still detected by its value); a data type uses its table entry.
static void WriteVarDecl(std::ofstream& ofs, const VcdSignal& sig,
                         std::string_view name, uint32_t width) {
  const char* keyword = sig.data_type == VcdDataType::kNet
                            ? VcdVarTypeKeyword(sig)
                            : VcdDataTypeKeyword(sig.data_type);
  uint32_t size = VcdDataTypeSize(sig.data_type, width);
  ofs << "$var " << keyword << " " << size << " " << sig.ident << " " << name
      << " $end\n";
}

// Emit the $var declaration for a freshly registered signal, choosing the
// extended-VCD port form (§21.7.4.2) when the writer is recording $dumpports
// nodes and the standard data-type form (§21.7.5) otherwise.
static void WriteSignalVarDecl(std::ofstream& ofs, const VcdSignal& sig,
                               std::string_view name, uint32_t width,
                               bool port_nodes) {
  if (port_nodes) {
    WritePortVarDecl(ofs, sig, name);
    return;
  }
  WriteVarDecl(ofs, sig, name, width);
}

void VcdWriter::RegisterSignal(const VcdSignalSpec& spec) {
  // §21.7.2.1: memories are not dumped in a VCD file. An unpacked-array
  // element reaches the writer under its element-select name (for example
  // mem[3]), so dropping any such registration keeps both its $var
  // declaration and every later value change for it out of the file, while a
  // packed vector -- registered under a bare identifier -- is still dumped in
  // full. The skip happens before the identifier code is assigned, so the
  // code sequence of the dumped objects is unaffected.
  if (spec.name.find('[') != std::string_view::npos) return;
  VcdSignal sig = MakeVcdSignal(spec, next_ident_, next_port_id_);
  signals_.push_back(sig);
  if (!ofs_.is_open()) return;
  WriteSignalVarDecl(ofs_, sig, spec.name, spec.width, port_nodes_);
}

void VcdWriter::WriteComment(std::string_view text) {
  if (!ofs_.is_open()) return;
  // The comment text -- one line or several -- sits between the $comment
  // keyword and the $end that closes the section.
  ofs_ << "$comment\n  " << text << "\n$end\n";
}

void VcdWriter::EndDefinitions() {
  if (!ofs_.is_open()) return;
  ofs_ << "$enddefinitions $end\n";
}

bool VcdWriter::AtSizeLimit() {
  if (size_limit_ == 0) return false;  // no limit configured
  if (limit_reached_) return true;     // already stopped
  if (!ofs_.is_open()) return false;
  std::streampos pos = ofs_.tellp();
  if (pos == std::streampos(-1)) return false;
  if (static_cast<uint64_t>(pos) < size_limit_) return false;
  // The file has reached the requested byte count: note it in the dump via a
  // §21.7.2.3 $comment section and stop recording any further value changes.
  WriteComment("Dump limit of " + std::to_string(size_limit_) +
               " bytes reached, dumping stopped.");
  limit_reached_ = true;
  return true;
}

void VcdWriter::WriteTimestamp(uint64_t time) {
  // §21.7.1.3: with the start gate armed, no simulation time is recorded until
  // a $dumpvars checkpoint has started the dump.
  if (!ofs_.is_open() || !enabled_ || !dump_started_) return;
  if (AtSizeLimit()) return;
  // §21.7.2.4: one simulation_time command introduces all the records of its
  // time unit; when a checkpoint already stamped this time, the value changes
  // that follow belong to the same #<time> group and no marker is repeated.
  if (have_time_ && time == last_time_) return;
  ofs_ << "#" << time << "\n";
  last_time_ = time;
  have_time_ = true;
}

void VcdWriter::EnsureTimestamp(uint64_t time) {
  if (!ofs_.is_open()) return;
  if (have_time_ && time == last_time_) return;
  ofs_ << "#" << time << "\n";
  last_time_ = time;
  have_time_ = true;
}

// Maps a single 4-state logic bit, given its aval and bval components, to the
// VCD value character: 0, 1, x, or z (§21.7.2.1).
static char LogicBitToChar(bool aval, bool bval) {
  if (!bval && !aval) return '0';
  if (!bval && aval) return '1';
  if (bval && aval) return 'x';  // x = (aval=1, bval=1)
  return 'z';                    // z = (aval=0, bval=1)
}

// Table 21-8: a shortened vector value is reconstructed by left-extending it
// according to its most significant retained digit. The values 0 and 1 extend
// with 0, an x extends with x, and a z extends with z.
static char VcdLeftExtendFill(char digit) {
  if (digit == 'x') return 'x';
  if (digit == 'z') return 'z';
  return '0';
}

// Returns the 4-state digit character for bit i of the signal's value, counting
// from the signal's own least significant bit and treating bits beyond the
// stored words as 0. §21.7.5: a structure member starts at bit_offset within
// the structure's shared value, so the offset shifts the whole window; an
// ordinary object leaves it at zero and reads its value directly.
static char VcdBitChar(const VcdSignal& sig, int32_t i) {
  uint32_t abs_bit = static_cast<uint32_t>(i) + sig.bit_offset;
  uint32_t word_idx = abs_bit / 64;
  uint32_t bit_idx = abs_bit % 64;
  uint64_t mask = uint64_t{1} << bit_idx;
  bool a = false;
  bool b = false;
  if (word_idx < sig.var->value.nwords) {
    a = (sig.var->value.words[word_idx].aval & mask) != 0;
    b = (sig.var->value.words[word_idx].bval & mask) != 0;
  }
  return LogicBitToChar(a, b);
}

// The signal's current value as 4-state digits, most significant bit first.
static std::string VcdSignalDigits(const VcdSignal& sig) {
  std::string digits;
  digits.reserve(sig.width);
  for (int32_t i = static_cast<int32_t>(sig.width) - 1; i >= 0; --i) {
    digits.push_back(VcdBitChar(sig, i));
  }
  return digits;
}

void VcdWriter::WriteScalarChange(const VcdSignal& sig) {
  if (!sig.var) return;
  // The aval/bval pair is read bit-wise so x=(1,1) stays distinct from
  // z=(0,1); a numeric projection would collapse both to 0 and misreport x.
  ofs_ << VcdBitChar(sig, 0) << sig.ident << "\n";
}

void VcdWriter::WriteVectorChange(const VcdSignal& sig) {
  if (!sig.var) return;
  // Build the full-width value with the most significant bit first.
  std::string digits = VcdSignalDigits(sig);
  // §21.7.2.2: vectors are written in the shortest right-justified form. A
  // leading digit is redundant when the left-extension rule applied to the
  // digit that would replace it regenerates that leading digit, so drop such
  // digits while always keeping at least one.
  size_t start = 0;
  while (start + 1 < digits.size() &&
         digits[start] == VcdLeftExtendFill(digits[start + 1])) {
    ++start;
  }
  // No white space between the base letter and the value digits, and exactly
  // one white space between the value digits and the identifier code.
  ofs_ << 'b' << (digits.c_str() + start) << ' ' << sig.ident << "\n";
}

void VcdWriter::WriteRealChange(const VcdSignal& sig) {
  if (!sig.var) return;
  // The stored value is the IEEE Std 754 double-precision bit pattern; recover
  // the number and print it with %.16g so the full 53-bit mantissa survives the
  // round-trip through the dump file.
  uint64_t bits = sig.var->value.ToUint64();
  double d = 0.0;
  std::memcpy(&d, &bits, sizeof(double));
  char buf[64];
  std::snprintf(buf, sizeof(buf), "%.16g", d);
  ofs_ << "r" << buf << " " << sig.ident << "\n";
}

void VcdWriter::WritePortValueChange(const VcdSignal& sig) {
  if (!sig.var) return;
  // §21.7.4.3 (Syntax 21-29): value ::= p port_value 0_strength_component
  // 1_strength_component. The key character p marks a port and is written with
  // no space before the port_value.
  ofs_ << 'p';
  // port_value: the binary state of the port (§21.7.4.1 — port values are given
  // in binary form as 0, 1, x, or z). The extended format dumps the whole
  // vector, most significant bit first; a scalar contributes a single state
  // character.
  bool driven = false;
  for (int32_t i = static_cast<int32_t>(sig.width) - 1; i >= 0; --i) {
    char c = VcdBitChar(sig, i);
    if (c != 'z') driven = true;
    ofs_ << c;
  }
  // The strength0 and strength1 components are each one of the eight
  // SystemVerilog strength values, encoded as the digit 0 highz, 1 small, 2
  // medium, 3 weak, 4 large, 5 pull, 6 strong, 7 supply. The model does not
  // track per-port drive strength, so a driven port is reported at strong
  // strength and a high-impedance port at highz strength for both components.
  char strength = driven ? '6' : '0';
  ofs_ << strength << strength;
  // identifier_code: the port's integer code preceded by <, exactly as written
  // in its $var declaration (§21.7.4.2). One space separates the value from it.
  ofs_ << " <" << sig.port_id << "\n";
}

void VcdWriter::WriteSignalChange(VcdSignal& sig) {
  // §21.7.2.2: an event is dumped in the scalar format, but its value
  // character carries no meaning -- only the identifier code matters, and the
  // record is a marker that the event triggered during the current time step.
  // So a marker is written only when the trigger stamp matches the time of the
  // last recorded timestamp; an untriggered event contributes nothing to a
  // checkpoint or to a per-timestep change scan.
  if (sig.var && sig.var->is_event) {
    if (sig.var->triggered_ticks == last_time_) {
      ofs_ << '1' << sig.ident << "\n";
    }
    return;
  }
  if (sig.var && sig.var->value.is_real) {
    WriteRealChange(sig);
  } else if (port_nodes_) {
    // §21.7.4.3: an extended VCD file produced by $dumpports records value
    // changes in the port form (p<port_value> with strength components and the
    // integer identifier code) rather than the 4-state form.
    WritePortValueChange(sig);
  } else if (sig.width == 1) {
    WriteScalarChange(sig);
  } else {
    WriteVectorChange(sig);
  }
  // §21.7.5: a structure member records the slice it just emitted instead of
  // resyncing the shared variable, which its siblings still need untouched so
  // each of them can detect its own next change.
  if (sig.is_field) {
    sig.prev_digits = VcdSignalDigits(sig);
    sig.has_prev_digits = true;
    return;
  }
  // The recorded state now matches the file: resync the previous value so the
  // next time increment's change detection compares against what was last
  // emitted. Assignments replace the value vector rather than mutating it in
  // place (edge detection relies on the same property), so this shallow copy
  // snapshots the emitted words.
  if (sig.var) sig.var->prev_value = sig.var->value;
}

void VcdWriter::WriteSignalAllX(const VcdSignal& sig) {
  // §21.7.1.3: a real number has no unknown state and its VCD value form is
  // the r-prefixed real (§21.7.2.1), so the suspend checkpoint records a real
  // variable as r0 rather than an ill-formed bit-form x.
  if (sig.var && sig.var->value.is_real) {
    ofs_ << "r0 " << sig.ident << "\n";
  } else if (sig.width == 1) {
    ofs_ << "x" << sig.ident << "\n";
  } else {
    ofs_ << "bx " << sig.ident << "\n";
  }
}

// §21.7.4.1 (Syntax 21-27): the simulation_keyword commands of an extended VCD
// file are the $dumpports task family, so a writer emitting the port-form file
// keys each checkpoint section with the extended keyword. Outside the port-node
// form the 4-state keyword of Syntax 21-20 is kept -- including by the extended
// file that reuses the 4-state machinery under the §21.7.4.1 construct-name
// equivalence rule, since those matching names stay equivalent across formats.
static const char* CheckpointKeyword(bool port_nodes, const char* four_state,
                                     const char* extended) {
  return port_nodes ? extended : four_state;
}

static bool HasValueChanged(const VcdSignal& sig) {
  // §21.7.5: every member of an unpacked structure shares one backing
  // variable, so the variable-wide previous value cannot say which member
  // moved -- the first member emitted would resync it and mask its siblings.
  // A member therefore compares its own slice against the digits it last
  // emitted, which makes each member's change detection independent.
  if (sig.is_field) {
    return !sig.has_prev_digits || VcdSignalDigits(sig) != sig.prev_digits;
  }
  // A variable that no edge control ever resynced has no recorded previous
  // value; treat it as changed so its first recording establishes the
  // baseline (WriteSignalChange resyncs after emitting) instead of reading
  // through an unset word array.
  const Logic4Vec& prev = sig.var->prev_value;
  if (prev.words == nullptr || prev.nwords < sig.var->value.nwords) return true;
  for (uint32_t w = 0; w < sig.var->value.nwords; ++w) {
    if (sig.var->value.words[w].aval != prev.words[w].aval ||
        sig.var->value.words[w].bval != prev.words[w].bval) {
      return true;
    }
  }
  return false;
}

void VcdWriter::DumpAllValues() {
  if (!ofs_.is_open() || !enabled_) return;
  if (AtSizeLimit()) return;
  // §21.7.1.3: the $dumpvars checkpoint starts the value change dumping; from
  // the end of this time unit onward, per-timestep changes are recorded.
  dump_started_ = true;
  ofs_ << CheckpointKeyword(port_nodes_, "$dumpvars", "$dumpports") << "\n";
  for (auto& sig : signals_) {
    WriteSignalChange(sig);
  }
  ofs_ << "$end\n";
}

void VcdWriter::DumpSelectedValues(const std::vector<std::string_view>& names) {
  if (!ofs_.is_open() || !enabled_) return;
  if (AtSizeLimit()) return;
  dump_started_ = true;  // §21.7.1.3: the checkpoint starts the dump
  ofs_ << CheckpointKeyword(port_nodes_, "$dumpvars", "$dumpports") << "\n";
  for (auto& sig : signals_) {
    bool wanted = false;
    for (auto name : names) {
      if (sig.name == name) {
        wanted = true;
        break;
      }
    }
    if (wanted) WriteSignalChange(sig);
  }
  ofs_ << "$end\n";
}

// §21.7.1.2: decide whether a $dumpvars scope list selects one signal. A scope
// that exactly names the signal is an individual variable and is always dumped
// -- the level count does not apply to individual variables. Otherwise the
// scope names a module instance: a signal lies beneath it when its hierarchical
// name begins with "scope.". The level count bounds how far below the module to
// descend -- the module's own variables sit one level down, a sub-instance's
// variables two, and so on -- with 0 meaning every level below.
static bool ScopeSelectsSignal(std::string_view sig_name,
                               const std::vector<std::string_view>& scopes,
                               uint64_t level) {
  for (std::string_view s : scopes) {
    if (sig_name == s) return true;
    if (sig_name.size() > s.size() + 1 && sig_name.substr(0, s.size()) == s &&
        sig_name[s.size()] == '.') {
      std::string_view rest = sig_name.substr(s.size() + 1);
      uint64_t depth = 1;
      for (char c : rest) {
        if (c == '.') ++depth;
      }
      if (level == 0 || depth <= level) return true;
    }
  }
  return false;
}

void VcdWriter::DumpScopeSelectedValues(
    const std::vector<std::string_view>& names, uint64_t level) {
  if (!ofs_.is_open() || !enabled_) return;
  if (AtSizeLimit()) return;
  dump_started_ = true;  // §21.7.1.3: the checkpoint starts the dump
  ofs_ << CheckpointKeyword(port_nodes_, "$dumpvars", "$dumpports") << "\n";
  for (auto& sig : signals_) {
    if (ScopeSelectsSignal(sig.name, names, level)) WriteSignalChange(sig);
  }
  ofs_ << "$end\n";
}

// §21.7.2.4: the illustrated file places each checkpoint section after the
// simulation_time command of the time unit its task executed in (#500 then the
// $dumpvars section, #535 then $dumpall, #1000 then $dumpoff, #2000 then
// $dumpon). Each timed form re-checks the untimed form's emission conditions
// first so a checkpoint that will not be emitted stamps no orphan time marker.
void VcdWriter::DumpAllValues(uint64_t time) {
  if (!ofs_.is_open() || !enabled_) return;
  if (AtSizeLimit()) return;
  EnsureTimestamp(time);
  DumpAllValues();
}

void VcdWriter::DumpScopeSelectedValues(
    const std::vector<std::string_view>& names, uint64_t level, uint64_t time) {
  if (!ofs_.is_open() || !enabled_) return;
  if (AtSizeLimit()) return;
  EnsureTimestamp(time);
  DumpScopeSelectedValues(names, level);
}

void VcdWriter::DumpAll(uint64_t time) {
  if (!ofs_.is_open() || !enabled_) return;
  if (AtSizeLimit()) return;
  EnsureTimestamp(time);
  DumpAll();
}

void VcdWriter::DumpOff(uint64_t time) {
  if (!ofs_.is_open()) return;
  EnsureTimestamp(time);
  DumpOff();
}

void VcdWriter::DumpOn(uint64_t time) {
  if (!ofs_.is_open()) return;
  EnsureTimestamp(time);
  DumpOn();
}

void VcdWriter::DumpAll() {
  if (!ofs_.is_open() || !enabled_) return;
  if (AtSizeLimit()) return;
  // The checkpoint records the present value of every selected variable,
  // regardless of whether that value changed during the current time step.
  ofs_ << CheckpointKeyword(port_nodes_, "$dumpall", "$dumpportsall") << "\n";
  for (auto& sig : signals_) {
    WriteSignalChange(sig);
  }
  ofs_ << "$end\n";
}

void VcdWriter::DumpOff() {
  if (!ofs_.is_open()) return;
  // The checkpoint records every selected variable as x, then dumping stops so
  // that no value changes are recorded until $dumpon is executed.
  ofs_ << CheckpointKeyword(port_nodes_, "$dumpoff", "$dumpportsoff") << "\n";
  for (auto& sig : signals_) {
    WriteSignalAllX(sig);
  }
  ofs_ << "$end\n";
  enabled_ = false;
}

void VcdWriter::DumpOn() {
  if (!ofs_.is_open()) return;
  // Recording resumes and a checkpoint of each variable's value at this time is
  // emitted so the dump reflects the current state.
  enabled_ = true;
  ofs_ << CheckpointKeyword(port_nodes_, "$dumpon", "$dumpportson") << "\n";
  for (auto& sig : signals_) {
    WriteSignalChange(sig);
  }
  ofs_ << "$end\n";
}

void VcdWriter::Flush() {
  if (!ofs_.is_open()) return;
  // Empty the stream's buffer into the file so its current contents are
  // observable to an external reader. No dump command is written and the
  // enabled state is left as it was, so dumping resumes seamlessly.
  ofs_.flush();
}

void VcdWriter::WriteVcdClose(uint64_t final_time) {
  if (!ofs_.is_open() || !extended_) return;
  // §21.7.3.6.1: the final keyword command of an extended VCD file marks the
  // end simulation time at the moment the file is closed. The time is written
  // as a value-change-style timestamp (#<time>), so the recorded end time
  // stands on its own even when no signal changed at that time.
  ofs_ << "$vcdclose #" << final_time << " $end\n";
}

void VcdWriter::SchedulePortDumpStart(std::vector<std::string> scopes,
                                      uint64_t time) {
  // §21.7.3.1: record the start so the end-of-timestep pass emits the opening
  // checkpoint; a non-empty scope_list also becomes the standing selection
  // filter for everything dumped from then on.
  port_start_pending_ = true;
  port_start_time_ = time;
  if (!port_start_scheduled_) {
    port_start_scheduled_ = true;
    port_scopes_ = std::move(scopes);
    port_selection_active_ = !port_scopes_.empty();
    return;
  }
  // §21.7.3.1: $dumpports may be invoked multiple times (all at one
  // simulation time), each call adding its selection to the one dump this
  // writer produces: named scopes union with those already listed, and a
  // call with no scope_list widens the selection to every registered object.
  if (scopes.empty() || !port_selection_active_) {
    port_scopes_.clear();
    port_selection_active_ = false;
    return;
  }
  for (auto& s : scopes) port_scopes_.push_back(std::move(s));
}

void VcdWriter::DumpChangedValues(uint64_t) {
  if (port_start_pending_) {
    // §21.7.3.1: the scheduled $dumpports start fires now that its execution
    // time unit has fully played out, so the opening checkpoint records the
    // selected objects' end-of-unit values. Level 1 bounds a named module
    // scope to its own objects: ports of instantiations below a listed scope
    // are not dumped.
    port_start_pending_ = false;
    if (port_scopes_.empty()) {
      DumpAllValues(port_start_time_);
    } else if (ofs_.is_open() && enabled_ && !AtSizeLimit()) {
      EnsureTimestamp(port_start_time_);
      std::vector<std::string_view> names(port_scopes_.begin(),
                                          port_scopes_.end());
      DumpScopeSelectedValues(names, 1);
    }
    // The checkpoint already reported every selected object at this time, so
    // no separate change records are needed for this pass.
    return;
  }
  // §21.7.1.3: while suspended by $dumpoff, and before an armed dump has been
  // started by $dumpvars, no value changes are dumped.
  if (!ofs_.is_open() || !enabled_ || !dump_started_) return;
  if (AtSizeLimit()) return;
  std::vector<std::string_view> selected(port_scopes_.begin(),
                                         port_scopes_.end());
  for (auto& sig : signals_) {
    if (!sig.var) continue;
    // §21.7.3.1: a $dumpports scope_list keeps objects outside the listed
    // module scopes -- including those of instantiations below a listed
    // scope -- out of the recording.
    if (port_selection_active_ && !ScopeSelectsSignal(sig.name, selected, 1)) {
      continue;
    }
    if (!HasValueChanged(sig)) continue;
    WriteSignalChange(sig);
  }
}

}  // namespace delta
