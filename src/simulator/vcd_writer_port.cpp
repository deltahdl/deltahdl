// The §21.7.4.3 half of the extended VCD file: one port's value change, the two
// strength components that follow it, and the §21.7.4.3.1 state character each
// bit is spelled with. The 4-state value changes, the declarations and the
// checkpoints are in vcd_writer.cpp; what separates the two is the port form,
// which §21.7.3.1 gives $dumpports alone.
#include <cstdint>
#include <fstream>
#include <string_view>

#include "common/types.h"
#include "parser/ast_type.h"
#include "simulator/net.h"
#include "simulator/variable.h"
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
// reduces two strengths to one takes "the stronger of the two", so the stronger
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
// Each list is longer than four. d/u on an input and l/h on an output mark two
// or more active drivers, and A a B b C c f mark an input and an output
// disagreeing (§21.7.4.3.2). Both describe the two ends of a port separately,
// which this model does not, so only the four values a driver here resolves to
// are mapped and nothing is invented for the rest.
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
  // inout is both ends at once, which is what 0 and 1 there stand for ("both
  // input and output are active with 0/1 value"), and a dumped object that is
  // no port at all has no direction to state.
  return "01?F";
}

// §21.7.4.3.1: the state character a port record reports one bit with. Syntax
// 21-29 is the grammar the record is parsed by and its port_value admits only
// these three lists; §21.7.4.1's sentence that port values are "specified in
// binary format by 0, 1, x, or z values" describes the file in general terms,
// and following it would write x and z, which no list carries, and would make
// every record read as direction-unknown. Where the two disagree the grammar
// is what a reader parses by, so the grammar wins.
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
    ofs_ << VcdPortStateChar(c, sig.direction);
  }
  WritePortStrengthComponents(ofs_, sig, driven);
  // identifier_code: the port's integer code preceded by <, exactly as written
  // in its $var declaration (§21.7.4.2). One space separates the value from it.
  ofs_ << " <" << sig.port_id << "\n";
}

}  // namespace delta
