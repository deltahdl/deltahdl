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

static char VcdStrengthDigit(Strength s) {
  return static_cast<char>('0' + static_cast<uint8_t>(s));
}

static char VcdUnresolvedStrengthDigit(bool driven) {
  return driven ? '6' : '0';
}

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

static std::string_view VcdPortStateList(Direction direction) {
  switch (direction) {
    case Direction::kInput:
      return "DUNZ";
    case Direction::kOutput:
      return "LHXT";
    default:
      break;
  }
  return "01?F";
}

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

static char DriverBitChar(const Logic4Vec& driver, uint32_t bit) {
  if (bit / 64 >= driver.nwords) return 'z';
  bool aval = (driver.words[bit / 64].aval >> (bit % 64)) & 1;
  bool bval = (driver.words[bit / 64].bval >> (bit % 64)) & 1;
  if (!bval) return aval ? '1' : '0';
  return aval ? 'x' : 'z';
}

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

static char SameValueEndsChar(const PortEnd& in, const PortEnd& out) {
  bool high = in.value == '1';
  if (in.strong == out.strong) return high ? '1' : '0';
  if (in.strong) return high ? 'u' : 'd';
  return high ? 'h' : 'l';
}

static char BothEndsChar(const PortEnd& in, const PortEnd& out) {
  if (in.value == out.value && in.value != 'x')
    return SameValueEndsChar(in, out);
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
  ofs_ << 'p';
  bool driven = false;
  for (int32_t i = static_cast<int32_t>(sig.width) - 1; i >= 0; --i) {
    char c = VcdBitChar(sig, i);
    if (c != 'z') driven = true;
    ofs_ << VcdPortBitChar(sig, static_cast<uint32_t>(i), c);
  }
  WritePortStrengthComponents(ofs_, sig, driven);
  ofs_ << " <" << sig.port_id << "\n";
}

}  // namespace delta
