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
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

void SetBit(std::vector<Logic4Word>& words, uint32_t k, bool a, bool b) {
  const uint64_t kMask = uint64_t{1} << (k % 64);
  if (a) words[k / 64].aval |= kMask;
  if (b) words[k / 64].bval |= kMask;
}

void Negate(std::vector<Logic4Word>& words) {
  uint64_t carry = 1;
  for (Logic4Word& word : words) {
    word.aval = ~word.aval + carry;
    carry = (carry != 0 && word.aval == 0) ? 1 : 0;
  }
}

void FillPattern(std::vector<Logic4Word>& words, uint64_t pattern,
                 bool negative) {
  words[0].aval = pattern;
  for (std::size_t i = 1; i < words.size(); ++i) {
    words[i].aval = negative ? ~uint64_t{0} : 0;
  }
}

void FillRounded(std::vector<Logic4Word>& words, double real) {
  const int64_t kRounded = std::llround(real);
  FillPattern(words, static_cast<uint64_t>(kRounded), kRounded < 0);
}

int DigitValue(char c) {
  if (c >= '0' && c <= '9') return c - '0';
  if (c >= 'a' && c <= 'f') return c - 'a' + 10;
  return -1;
}

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

void MultiplyAddTen(std::vector<Logic4Word>& words, uint64_t digit) {
  uint64_t carry = digit;
  for (Logic4Word& word : words) {
    const uint64_t kLow = ((word.aval & 0xFFFFFFFFu) * 10) + carry;
    const uint64_t kHigh = ((word.aval >> 32) * 10) + (kLow >> 32);
    word.aval = (kHigh << 32) | (kLow & 0xFFFFFFFFu);
    carry = kHigh >> 32;
  }
}

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

void VectorBits(const s_vpi_vecval* vector, uint32_t width,
                std::vector<Logic4Word>& words) {
  for (uint32_t k = 0; k < width; ++k) {
    const s_vpi_vecval& element = vector[k / 32];
    SetBit(words, k, ((element.aval >> (k % 32)) & 1) != 0,
           ((element.bval >> (k % 32)) & 1) != 0);
  }
}

void ScalarBit(int scalar, std::vector<Logic4Word>& words) {
  SetBit(words, 0, scalar == kVpi1 || scalar == kVpiX,
         scalar == kVpiX || scalar == kVpiZ);
}

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

int VpiObjectTimeUnit(const VpiObject& obj, int sim_unit) {
  for (const VpiObject* at = &obj; at != nullptr; at = at->parent) {
    if (VpiIsInstanceType(at->type)) return at->time_unit;
  }
  return sim_unit;
}

uint64_t VpiPutDelayTicks(const VpiObject& obj, const s_vpi_time& time,
                          int sim_unit) {
  if (time.type != kVpiScaledRealTime) {
    return (uint64_t{time.high} << 32) | time.low;
  }
  const double kScale =
      std::pow(10.0, VpiObjectTimeUnit(obj, sim_unit) - sim_unit);
  return static_cast<uint64_t>(std::llround(time.real * kScale));
}

}  // namespace delta
