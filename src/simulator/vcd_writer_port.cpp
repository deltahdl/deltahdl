// The §21.7.4.3 half of the extended VCD file: one port's value change, the two
// strength components that follow it, and the §21.7.4.3.1 state character each
// bit is spelled with. The 4-state value changes, the declarations and the
// checkpoints are in vcd_writer.cpp; what separates the two is the port form,
// which §21.7.3.1 gives $dumpports alone.
#include <algorithm>
#include <cctype>
#include <cstddef>
#include <cstdint>
#include <fstream>
#include <ostream>
#include <string_view>

#include "common/types.h"
#include "parser/ast_type.h"
#include "simulator/net.h"
#include "simulator/vcd_writer.h"

namespace delta {

// §21.7.4.3: a strength component is one of the eight SystemVerilog strengths,
// written as the digit 0 highz, 1 small, 2 medium, 3 weak, 4 large, 5 pull, 6
// strong, 7 supply. Strength (common/types.h) is numbered the same way, so the
// digit is the enum value.
static char VcdStrengthDigit(Strength s) {
  return static_cast<char>('0' + static_cast<uint8_t>(s));
}

// §21.7.4.3: both strength components of a port whose drive strength the model
// leaves unresolved. §21.7.4.3.2 counts primitives, continuous assignments and
// procedural continuous assignments as drivers, so a port_value other than z
// says a driver is active, and §28.6 gives a driver written without a drive
// strength specification strong0 and strong1 -- the digit 6. A z port_value
// says no driver is active, which is highz, the digit 0.
//
// Two kinds of object are answered here. An object that is not a net has no
// drive strength to resolve. So has a net Net::Resolve computed no strength
// for: one held by force, whose drivers it skips (net.cpp: is_forced returns
// before resolution), and one driven to x, which §28.12 places on neither the
// 0 side nor the 1 side.
static char VcdUnresolvedStrengthDigit(bool driven) {
  return driven ? '6' : '0';
}

// §21.7.4.3: write the 0_strength_component and the 1_strength_component of one
// port value change. They report the strength0 and the strength1 specification
// for the port, and net resolution settles both: NetStrength keeps the strength
// of the drive on the 0 side and on the 1 side separately, so its s0 fields
// answer the first component and its s1 fields the second.
//
// Each component is a single digit while §28.12 lets a resolved strength be
// ambiguous -- a range of levels rather than one level. §21.7.4.3.2 does not
// say what one digit reports for a range. The one rule it does give that
// reduces two strengths to one keeps whichever is stronger, so the stronger
// bound of the range is what is written here.
static void WritePortStrengthComponents(std::ofstream& ofs,
                                        const VcdSignal& sig, bool driven) {
  if (sig.net != nullptr) {
    const NetStrength& resolved = sig.net->resolved_strength;
    if (resolved.s0_hi != Strength::kHighz ||
        resolved.s1_hi != Strength::kHighz) {
      ofs << VcdStrengthDigit(resolved.s0_hi)
          << VcdStrengthDigit(resolved.s1_hi);
      return;
    }
  }
  char digit = VcdUnresolvedStrengthDigit(driven);
  ofs << digit << digit;
}

// §21.7.4.3.1: the four state characters one direction's list gives the values
// this model resolves -- low, high, unknown and three-state, in that order.
//
// Each list is longer than four: d/u on an input and l/h on an output mark two
// or more active drivers (VcdPortBitChar), and the unknown-direction list's
// A a B b C c f mark an inout's two ends disagreeing (InoutBitChar).
static std::string_view VcdPortStateList(Direction direction) {
  switch (direction) {
    case Direction::kInput:
      // D low, U high, N unknown, Z three-state.
      return "DUNZ";
    case Direction::kOutput:
      // L low, H high, X unknown (do not care), T three-state.
      return "LHXT";
    default:
      break;
  }
  // The unknown-direction list: 0 low, 1 high, ? unknown, F three-state. An
  // inout is both ends at once, which is what 0 and 1 there stand for: input
  // and output both active, at 0 or at 1. A dumped object that is
  // no port at all has no direction to state.
  return "01?F";
}

// §21.7.4.3.1: the state character a port record reports one bit with. Syntax
// 21-29 is the grammar the record is parsed by and its port_value admits only
// these three lists; §21.7.4.1's sentence giving port values in binary as 0,
// 1, x or z describes the file in general terms, and following it would write
// x and z, which no list carries, and would make every record read as
// direction-unknown. Where the two disagree the grammar is what a reader
// parses by, so the grammar wins.
static char VcdPortStateChar(char four_state, Direction direction) {
  std::string_view list = VcdPortStateList(direction);
  switch (four_state) {
    case '0':
      return list[0];
    case '1':
      return list[1];
    case 'x':
      return list[2];
    default:
      break;
  }
  return list[3];
}

// §21.7.4.2 (Syntax 21-28): $var port <size> <<id> <reference> $end. The
// var_type keyword is always port; the size is the declared index range of a
// bus or 1 for a single-bit port; the identifier code is the integer preceded
// by <. At least one space separates each syntactical element.
void WritePortVarDecl(std::ostream& ofs, const VcdSignal& sig,
                      std::string_view name) {
  ofs << "$var port ";
  if (sig.msb >= 0 && sig.lsb >= 0) {
    ofs << "[" << sig.msb << ":" << sig.lsb << "]";
  } else {
    ofs << "1";
  }
  ofs << " <" << sig.port_id << " " << name << " $end\n";
}

// The value one driver puts on bit `bit` of its net: 0, 1, x or z, read from
// its 4-state words as VcdBitChar reads a dumped object's.
static char DriverBitChar(const Logic4Vec& driver, uint32_t bit) {
  if (bit / 64 >= driver.nwords) return 'z';
  bool aval = (driver.words[bit / 64].aval >> (bit % 64)) & 1;
  bool bval = (driver.words[bit / 64].bval >> (bit % 64)) & 1;
  if (!bval) return aval ? '1' : '0';
  return aval ? 'x' : 'z';
}

// §21.7.4.3.1 (printed pages 700-701): an input whose test-fixture side, or an
// output whose device side, has two or more drivers active at the bit's value
// reports d or u, or l or h, in place of D or U, or L or H. An input's
// test-fixture side is the signal the parent connected to it, where that is a
// plain name; the port's own net holds only the connection there.
static bool HasTwoActiveDrivers(const VcdSignal& sig, uint32_t bit,
                                char four_state) {
  const Net* net = sig.direction == Direction::kInput && sig.source_net
                       ? sig.source_net
                       : sig.net;
  if (net == nullptr) return false;
  return std::ranges::count_if(net->drivers, [&](const Logic4Vec& driver) {
           return DriverBitChar(driver, bit) == four_state;
         }) >= 2;
}

// §21.7.4.3.2: one end of an inout port at one bit -- the input end the
// drivers outside its instance, the output end those inside. `value` is what
// its active drivers settle on, z where none is active and x where they
// disagree; `strong` whether the strongest of them is in the strong range,
// 7 to 5, rather than the weak one, 4 to 1; `connected` whether any driver
// stands at that end at all.
struct PortEnd {
  char value = 'z';
  bool strong = false;
  bool connected = false;
};

static Strength DriverStrengthFor(const Net& net, size_t k, char value) {
  if (k >= net.driver_strengths.size()) return Strength::kStrong;
  const DriverStrength& ds = net.driver_strengths[k];
  if (value == '0') return ds.s0;
  if (value == '1') return ds.s1;
  return std::max(ds.s0, ds.s1);
}

static PortEnd EndOfPort(const Net& net, uint32_t bit, std::string_view inst,
                         bool inside) {
  PortEnd end;
  for (size_t k = 0; k < net.drivers.size(); ++k) {
    std::string_view origin =
        k < net.driver_origins.size() ? net.driver_origins[k] : "";
    if (origin.starts_with(inst) != inside) continue;
    end.connected = true;
    char value = DriverBitChar(net.drivers[k], bit);
    if (value == 'z') continue;
    end.value = end.value == 'z' || end.value == value ? value : 'x';
    end.strong |= DriverStrengthFor(net, k, value) >= Strength::kPull;
  }
  return end;
}

// §21.7.4.3.1 and §21.7.4.3.2: the character of an inout bit both of whose
// ends are active. Ends at one value are a conflict, resolved by strength
// range: the same range gives 0 or 1, a strong input over a weak output d or
// u, a weak input under a strong output l or h. Ends at different values name
// the pair from the unknown-direction list, input first: A for 0 and 1, a for
// 0 and x, B for 1 and 0, b for 1 and x, C for x and 0, c for x and 1, and ?
// where both are unknown.
static char BothEndsChar(const PortEnd& in, const PortEnd& out) {
  if (in.value == out.value && in.value != 'x') {
    bool high = in.value == '1';
    if (in.strong == out.strong) return high ? '1' : '0';
    if (in.strong) return high ? 'u' : 'd';
    return high ? 'h' : 'l';
  }
  switch (in.value) {
    case '0':
      return out.value == '1' ? 'A' : 'a';
    case '1':
      return out.value == '0' ? 'B' : 'b';
    default:
      break;
  }
  if (out.value == '0') return 'C';
  return out.value == '1' ? 'c' : '?';
}

// §21.7.4.3.1: an inout port bit, from its two ends. With neither end
// connected it is F, with both three-stated f; with one end active the
// unknown-direction character of the resolved value stands.
static char InoutBitChar(const VcdSignal& sig, uint32_t bit, char four_state) {
  std::string_view inst = sig.name.substr(0, sig.name.rfind('.') + 1);
  PortEnd in = EndOfPort(*sig.net, bit, inst, false);
  PortEnd out = EndOfPort(*sig.net, bit, inst, true);
  if (!in.connected && !out.connected) return 'F';
  if (in.value == 'z' && out.value == 'z') return 'f';
  if (in.value == 'z' || out.value == 'z')
    return VcdPortStateChar(four_state, sig.direction);
  return BothEndsChar(in, out);
}

// §21.7.4.3.1: the state character a port record reports bit `bit` with.
static char VcdPortBitChar(const VcdSignal& sig, uint32_t bit,
                           char four_state) {
  if (sig.direction == Direction::kInout && sig.net != nullptr)
    return InoutBitChar(sig, bit, four_state);
  char c = VcdPortStateChar(four_state, sig.direction);
  bool sided =
      sig.direction == Direction::kInput || sig.direction == Direction::kOutput;
  if (!sided || (four_state != '0' && four_state != '1') ||
      !HasTwoActiveDrivers(sig, bit, four_state))
    return c;
  return static_cast<char>(std::tolower(static_cast<unsigned char>(c)));
}

void VcdWriter::WritePortValueChange(const VcdSignal& sig) {
  if (!sig.var) return;
  // §21.7.4.3 (Syntax 21-29): value ::= p port_value 0_strength_component
  // 1_strength_component. The key character p marks a port and is written with
  // no space before the port_value.
  ofs_ << 'p';
  // port_value: the state of the port, from the §21.7.4.3.1 list its declared
  // direction names. The extended format dumps the whole vector, most
  // significant bit first; a scalar contributes a single state character.
  bool driven = false;
  for (int32_t i = static_cast<int32_t>(sig.width) - 1; i >= 0; --i) {
    char c = VcdBitChar(sig, i);
    if (c != 'z') driven = true;
    ofs_ << VcdPortBitChar(sig, static_cast<uint32_t>(i), c);
  }
  WritePortStrengthComponents(ofs_, sig, driven);
  // identifier_code: the port's integer code preceded by <, exactly as written
  // in its $var declaration (§21.7.4.2). One space separates the value from it.
  ofs_ << " <" << sig.port_id << "\n";
}

}  // namespace delta
