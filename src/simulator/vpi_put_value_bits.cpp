#include <algorithm>
#include <cctype>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <memory>
#include <string_view>
#include <utility>
#include <vector>

#include "common/types.h"
#include "simulator/scheduler.h"
#include "simulator/variable.h"
#include "simulator/vpi_collection_elements.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

// Bit `k` of `words`, its a and b bits set as `a` and `b` say; x is (1,1) and
// z (0,1), the encoding Figure 38-8 gives.
void SetBit(std::vector<Logic4Word>& words, uint32_t k, bool a, bool b) {
  const uint64_t kMask = uint64_t{1} << (k % 64);
  if (a) words[k / 64].aval |= kMask;
  if (b) words[k / 64].bval |= kMask;
}

// The two's complement of the value `words` hold, in place.
void Negate(std::vector<Logic4Word>& words) {
  uint64_t carry = 1;
  for (Logic4Word& word : words) {
    word.aval = ~word.aval + carry;
    carry = (carry != 0 && word.aval == 0) ? 1 : 0;
  }
}

// `pattern` in the low 64 bits, and above it every bit `negative` says the
// sign extends into.
void FillPattern(std::vector<Logic4Word>& words, uint64_t pattern,
                 bool negative) {
  words[0].aval = pattern;
  for (std::size_t i = 1; i < words.size(); ++i) {
    words[i].aval = negative ? ~uint64_t{0} : 0;
  }
}

// §6.12.1: `real` converted to an integral value, rounded to the nearest
// integer, ties away from zero.
void FillRounded(std::vector<Logic4Word>& words, double real) {
  const int64_t kRounded = std::llround(real);
  FillPattern(words, static_cast<uint64_t>(kRounded), kRounded < 0);
}

// The value of the digit `c`, lowercase, in base 16 or below; -1 for a
// character that is no digit.
int DigitValue(char c) {
  if (c >= '0' && c <= '9') return c - '0';
  if (c >= 'a' && c <= 'f') return c - 'a' + 10;
  return -1;
}

// §38.15, Table 38-3 (vpiBinStrVal, vpiOctStrVal and vpiHexStrVal rows): the
// digits of `text` from the rightmost up, each `bits` bits of the value, an x
// or z digit of either case unknown in every bit it stands for; false where a
// character is no digit of the base.
bool DigitBits(std::string_view text, uint32_t bits, uint32_t width,
               std::vector<Logic4Word>& words) {
  uint32_t k = 0;
  for (auto it = text.rbegin(); it != text.rend() && k < width; ++it) {
    const char kDigit =
        static_cast<char>(std::tolower(static_cast<unsigned char>(*it)));
    const bool kUnknown = kDigit == 'x' || kDigit == 'z';
    const int kValue = kUnknown ? 0 : DigitValue(kDigit);
    if (kValue < 0 || kValue >= (1 << bits)) return false;
    for (uint32_t j = 0; j < bits && k < width; ++j, ++k) {
      const bool kSet = kUnknown ? kDigit == 'x' : ((kValue >> j) & 1) != 0;
      SetBit(words, k, kSet, kUnknown);
    }
  }
  return true;
}

// `words` times ten, plus `digit`, carried across every word.
void MultiplyAddTen(std::vector<Logic4Word>& words, uint64_t digit) {
  uint64_t carry = digit;
  for (Logic4Word& word : words) {
    const uint64_t kLow = ((word.aval & 0xFFFFFFFFu) * 10) + carry;
    const uint64_t kHigh = ((word.aval >> 32) * 10) + (kLow >> 32);
    word.aval = (kHigh << 32) | (kLow & 0xFFFFFFFFu);
    carry = kHigh >> 32;
  }
}

// §38.15, Table 38-3 (vpiDecStrVal row): the number `text` writes in decimal,
// a leading minus sign making it negative in two's complement; false where a
// character is no decimal digit.
bool DecimalBits(std::string_view text, std::vector<Logic4Word>& words) {
  const bool kNegative = text.starts_with('-');
  if (kNegative) text.remove_prefix(1);
  if (text.empty()) return false;
  for (const char kDigit : text) {
    if (kDigit < '0' || kDigit > '9') return false;
    MultiplyAddTen(words, static_cast<uint64_t>(kDigit - '0'));
  }
  if (kNegative) Negate(words);
  return true;
}

// §38.15, Table 38-3 (vpiStringVal row): each eight bits of the value one
// character of `text`, the last character the least significant.
void StringBits(std::string_view text, uint32_t width,
                std::vector<Logic4Word>& words) {
  uint32_t k = 0;
  for (auto it = text.rbegin(); it != text.rend() && k < width; ++it) {
    const auto kChar = static_cast<unsigned char>(*it);
    for (uint32_t j = 0; j < 8 && k < width; ++j, ++k) {
      SetBit(words, k, ((kChar >> j) & 1) != 0, false);
    }
  }
}

// §38.15 (Figure 38-8): the aval/bval words of a vpiVectorVal value, 32 bits
// of the value in each element of `vector`, the first the least significant.
void VectorBits(const s_vpi_vecval* vector, uint32_t width,
                std::vector<Logic4Word>& words) {
  for (uint32_t k = 0; k < width; ++k) {
    const s_vpi_vecval& element = vector[k / 32];
    SetBit(words, k, ((element.aval >> (k % 32)) & 1) != 0,
           ((element.bval >> (k % 32)) & 1) != 0);
  }
}

// The value of a vpiScalarVal or vpiStrengthVal's logic, `scalar`, in bit 0.
void ScalarBit(int scalar, std::vector<Logic4Word>& words) {
  SetBit(words, 0, scalar == kVpi1 || scalar == kVpiX,
         scalar == kVpiX || scalar == kVpiZ);
}

// The value of `value`, of a format whose text a string member holds, in
// `words`; false where that member is null or its text no number of the
// format.
bool TextBits(const s_vpi_value& value, uint32_t width,
              std::vector<Logic4Word>& words) {
  if (value.value.str == nullptr) return false;
  const std::string_view kText(value.value.str);
  switch (value.format) {
    case kVpiBinStrVal:
      return DigitBits(kText, 1, width, words);
    case kVpiOctStrVal:
      return DigitBits(kText, 3, width, words);
    case kVpiHexStrVal:
      return DigitBits(kText, 4, width, words);
    case kVpiDecStrVal:
      return DecimalBits(kText, words);
    default:
      StringBits(kText, width, words);
      return true;
  }
}

// The value of `value`, of a format a pointer member other than the string
// holds, in `words`; false where that pointer is null.
bool PointedBits(const s_vpi_value& value, uint32_t width,
                 std::vector<Logic4Word>& words) {
  switch (value.format) {
    case kVpiTimeVal:
      if (value.value.time == nullptr) return false;
      FillPattern(
          words,
          (uint64_t{value.value.time->high} << 32) | value.value.time->low,
          false);
      return true;
    case kVpiVectorVal:
      if (value.value.vector == nullptr) return false;
      VectorBits(value.value.vector, width, words);
      return true;
    default:
      if (value.value.strength == nullptr) return false;
      ScalarBit(value.value.strength->logic, words);
      return true;
  }
}

// §38.34: take out of the event queue the delayed puts pending on `target`
// that a put taking place at `at` under `mode` removes: every one for
// vpiInertialDelay, those later than it for vpiTransportDelay, and none for
// vpiPureTransportDelay.
void RemovePendingPuts(VpiObject& target, int mode, uint64_t at) {
  if (mode == vpiPureTransportDelay) return;
  for (VpiObject* event : target.scheduled_puts) {
    if (!event->scheduled) continue;
    if (mode == vpiTransportDelay && event->event_time <= at) continue;
    *event->put_superseded = true;
    event->scheduled = false;
  }
  std::erase_if(target.scheduled_puts,
                [](const VpiObject* event) { return !event->scheduled; });
}

}  // namespace

bool VpiPutValueBits(const s_vpi_value& value, uint32_t width,
                     std::vector<Logic4Word>& words) {
  if (width == 0) return false;
  words.assign((static_cast<std::size_t>(width) + 63) / 64, Logic4Word{0, 0});
  bool decoded = true;
  switch (value.format) {
    case kVpiIntVal:
      FillPattern(words, static_cast<uint64_t>(int64_t{value.value.integer}),
                  value.value.integer < 0);
      break;
    case kVpiRealVal:
      FillRounded(words, value.value.real);
      break;
    case kVpiScalarVal:
      ScalarBit(value.value.scalar, words);
      break;
    case kVpiBinStrVal:
    case kVpiOctStrVal:
    case kVpiHexStrVal:
    case kVpiDecStrVal:
    case kVpiStringVal:
      decoded = TextBits(value, width, words);
      break;
    case kVpiTimeVal:
    case kVpiVectorVal:
    case kVpiStrengthVal:
      decoded = PointedBits(value, width, words);
      break;
    default:
      return false;
  }
  if (!decoded) return false;
  if (width % 64 != 0) {
    const uint64_t kMask = (uint64_t{1} << (width % 64)) - 1;
    words.back().aval &= kMask;
    words.back().bval &= kMask;
  }
  return true;
}

uint32_t VpiPutWidth(const VpiObject& obj) {
  return obj.bit_offset >= 0 ? static_cast<uint32_t>(std::max(obj.size, 1))
                             : std::max(obj.var->value.width, uint32_t{1});
}

void VpiWriteDecodedBits(VpiObject& obj, const std::vector<Logic4Word>& bits,
                         uint32_t width) {
  Logic4Vec& whole = obj.var->value;
  const uint64_t kBase =
      obj.bit_offset >= 0 ? static_cast<uint64_t>(obj.bit_offset) : 0;
  for (uint32_t k = 0; k < width; ++k) {
    const uint64_t kBit = kBase + k;
    if (kBit / 64 >= whole.nwords) return;
    const uint64_t kMask = uint64_t{1} << (kBit % 64);
    const bool kA = ((bits[k / 64].aval >> (k % 64)) & 1) != 0;
    const bool kB = ((bits[k / 64].bval >> (k % 64)) & 1) != 0;
    Logic4Word& word = whole.words[kBit / 64];
    word.aval = (word.aval & ~kMask) | (kA ? kMask : 0);
    word.bval = (word.bval & ~kMask) | (kB ? kMask : 0);
  }
}

void VpiSchedulePut(VpiObject& obj, const s_vpi_value& value, int mode,
                    Scheduler& scheduler, VpiObject& event) {
  const uint32_t kWidth = VpiPutWidth(obj);
  std::vector<Logic4Word> bits;
  if (!VpiPutValueBits(value, kWidth, bits)) return;
  const uint64_t kAt = event.event_time;
  RemovePendingPuts(obj, mode, kAt);
  event.type = vpiSchedEvent;
  event.scheduled = true;
  event.put_superseded = std::make_shared<bool>(false);
  obj.scheduled_puts.push_back(&event);
  Event* queued = scheduler.GetEventPool().Acquire();
  queued->superseded = event.put_superseded;
  // The scheduler runs a superseded event's callback as well, so a put that a
  // cancel or a later put removed checks for that itself, before it reads the
  // vpiSchedEvent a cancel frees.
  queued->callback = [target = &obj, sched = &event, bits = std::move(bits),
                      kWidth, removed = event.put_superseded]() {
    if (*removed) return;
    sched->scheduled = false;
    VpiWriteDecodedBits(*target, bits, kWidth);
    target->var->NotifyWatchers();
    VpiStoreElementCopy(*target);
  };
  scheduler.ScheduleEvent(SimTime{kAt}, Region::kActive, queued);
}

uint64_t VpiPutDelayTicks(const VpiObject& obj, const s_vpi_time& time,
                          int sim_unit) {
  if (time.type != kVpiScaledRealTime) {
    return (uint64_t{time.high} << 32) | time.low;
  }
  const double kScale = std::pow(10.0, obj.time_unit - sim_unit);
  return static_cast<uint64_t>(std::llround(time.real * kScale));
}

}  // namespace delta
