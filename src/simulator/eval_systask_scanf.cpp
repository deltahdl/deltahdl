#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"
#include "simulator/eval_string.h"
#include "simulator/eval_systask_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/variable.h"

namespace delta {

static int SpecToBase(char spec) {
  char c =
      (spec >= 'A' && spec <= 'Z') ? static_cast<char>(spec - 'A' + 'a') : spec;
  if (c == 'd') return 10;
  if (c == 'h' || c == 'x') return 16;
  if (c == 'b') return 2;
  if (c == 'o') return 8;
  return 0;
}

static bool IsScanSpace(char c) {
  return c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\f' ||
         c == '\v';
}

static bool ScanArgHasUnknownBits(const Expr* arg, SimContext& ctx,
                                  Arena& arena) {
  if (!arg || arg->kind == ExprKind::kStringLiteral) return false;
  if (arg->kind == ExprKind::kIdentifier &&
      ctx.FindArrayInfo(arg->text) != nullptr) {
    return false;
  }
  Logic4Vec v = EvalExpr(arg, ctx, arena);
  for (uint32_t w = 0; w < v.nwords; ++w) {
    if (v.words[w].bval != 0) return true;
  }
  return false;
}

Logic4Vec ScanStringToVec(Arena& arena, const std::string& str,
                          uint32_t width) {
  auto vec = MakeLogic4VecVal(arena, width, 0);
  for (size_t i = 0; i < str.size() && i * 8 < width; ++i) {
    auto byte_idx = static_cast<uint32_t>(str.size() - 1 - i);
    uint32_t word = (byte_idx * 8) / 64;
    uint32_t bit = (byte_idx * 8) % 64;
    if (word < vec.nwords) {
      vec.words[word].aval |=
          static_cast<uint64_t>(static_cast<uint8_t>(str[i])) << bit;
    }
  }
  return vec;
}

void StoreRealField(Variable* var, Arena& arena, double d) {
  if (!var) return;
  uint64_t bits = 0;
  std::memcpy(&bits, &d, sizeof(double));
  uint32_t width = var->value.width ? var->value.width : 64;
  auto vec = MakeLogic4VecVal(arena, width, bits);
  vec.is_real = true;
  var->value = vec;
  var->NotifyWatchers();
}

enum class ScanFieldResult : std::uint8_t { kStop, kMatched, kSkipped };

namespace {
struct ScanCursor {
  const std::string& input;
  size_t& pos;
};

struct ScanInputField {
  const ScanCursor& cur;
  int width;
};

size_t ScanUpperLimit(const ScanCursor& cur, int width) {
  if (width > 0 && cur.pos + static_cast<size_t>(width) < cur.input.size())
    return cur.pos + static_cast<size_t>(width);
  return cur.input.size();
}

struct ScanDest {
  Variable* var = nullptr;
  bool is_string = false;
  const ArrayInfo* byte_array = nullptr;
  std::string_view name;
  const Expr* assign_back = nullptr;
};

void StoreScannedChars(const ScanDest& dst, const std::string& s,
                       SimContext& ctx, Arena& arena) {
  if (dst.byte_array != nullptr) {
    const ArrayInfo* ai = dst.byte_array;
    for (uint32_t i = 0; i < ai->size; ++i) {
      uint32_t idx =
          ai->is_descending ? (ai->lo + ai->size - 1 - i) : (ai->lo + i);
      std::string ename =
          std::string(dst.name) + "[" + std::to_string(idx) + "]";
      Variable* elem = ctx.FindVariable(ename);
      if (elem == nullptr) continue;
      uint8_t byte = i < s.size() ? static_cast<uint8_t>(s[i]) : 0;
      elem->value = MakeLogic4VecVal(arena, ai->elem_width, byte);
      elem->NotifyWatchers();
    }
    return;
  }
  if (dst.var == nullptr) return;
  if (dst.is_string) {
    dst.var->value =
        ScanStringToVec(arena, s, static_cast<uint32_t>(s.size()) * 8);
  } else {
    dst.var->value = ScanStringToVec(arena, s, dst.var->value.width);
  }
  dst.var->NotifyWatchers();
}

ScanFieldResult ScanCharField(ScanCursor cur, int width, const ScanDest& dst,
                              SimContext& ctx, Arena& arena) {
  int cnt = width > 0 ? width : 1;
  if (cur.pos >= cur.input.size()) return ScanFieldResult::kStop;
  std::string chars;
  for (int k = 0; k < cnt && cur.pos < cur.input.size(); ++k)
    chars += cur.input[cur.pos++];
  if (chars.size() == 1 && dst.var && !dst.is_string) {
    dst.var->value = MakeLogic4VecVal(arena, dst.var->value.width,
                                      static_cast<uint8_t>(chars[0]));
    dst.var->NotifyWatchers();
  } else {
    StoreScannedChars(dst, chars, ctx, arena);
  }
  return ScanFieldResult::kMatched;
}

ScanFieldResult ScanStringField(ScanCursor cur, int width, const ScanDest& dst,
                                SimContext& ctx, Arena& arena) {
  size_t limit = ScanUpperLimit(cur, width);
  std::string s;
  while (cur.pos < limit && !IsScanSpace(cur.input[cur.pos]))
    s += cur.input[cur.pos++];
  if (s.empty()) return ScanFieldResult::kStop;
  StoreScannedChars(dst, s, ctx, arena);
  return ScanFieldResult::kMatched;
}

double ScaleScannedTime(double d, SimContext& ctx) {
  const TimeFormatSpec& tf = ctx.GetTimeFormat();
  double p = std::pow(10.0, tf.precision_number);
  double scaled = d * p;
  d = std::floor(scaled + 0.5 + std::fabs(scaled) * 1e-12) / p;
  const TimeScale& ts = ActiveInstanceTimeScale(ctx);
  d *= std::pow(10.0, tf.units_number - static_cast<int>(ts.unit));
  if (ts.magnitude != 0) d /= ts.magnitude;
  return d;
}

ScanFieldResult ScanRealField(const ScanInputField& field, bool is_time,
                              Variable* var, SimContext& ctx, Arena& arena) {
  const ScanCursor& cur = field.cur;
  size_t limit = ScanUpperLimit(cur, field.width);
  std::string sub = cur.input.substr(cur.pos, limit - cur.pos);
  const char* c = sub.c_str();
  char* end = nullptr;
  double d = std::strtod(c, &end);
  if (end == c) return ScanFieldResult::kStop;
  cur.pos += static_cast<size_t>(end - c);
  if (is_time) d = ScaleScannedTime(d, ctx);
  StoreRealField(var, arena, d);
  return ScanFieldResult::kMatched;
}

uint32_t ScanRead32(const ScanCursor& cur, size_t at) {
  uint32_t x = 0;
  for (int b = 0; b < 4; ++b)
    x |= static_cast<uint32_t>(static_cast<uint8_t>(cur.input[at + b]))
         << (8 * b);
  return x;
}

uint32_t ScanChunkMask(uint32_t width, uint32_t off) {
  if (off + 32 <= width) return ~uint32_t{0};
  if (off >= width) return 0;
  return (uint32_t{1} << (width - off)) - 1;
}

ScanFieldResult ScanRawBinaryField(ScanCursor cur, Variable* var,
                                   Arena& arena) {
  uint32_t w = var ? var->value.width : 32;
  uint32_t nchunks = (w + 31) / 32;
  if (nchunks == 0) nchunks = 1;
  size_t need = static_cast<size_t>(nchunks) * 4;
  if (cur.pos + need > cur.input.size()) return ScanFieldResult::kStop;
  auto vec = MakeLogic4VecVal(arena, w, 0);
  for (uint32_t k = 0; k < nchunks; ++k) {
    uint32_t off = k * 32;
    uint64_t chunk = ScanRead32(cur, cur.pos + static_cast<size_t>(k) * 4) &
                     ScanChunkMask(w, off);
    uint32_t word = off / 64;
    if (word < vec.nwords) vec.words[word].aval |= chunk << (off % 64);
  }
  cur.pos += need;
  if (var) {
    var->value = vec;
    var->NotifyWatchers();
  }
  return ScanFieldResult::kMatched;
}

ScanFieldResult ScanFourStateField(ScanCursor cur, Variable* var,
                                   Arena& arena) {
  uint32_t w = var ? var->value.width : 32;
  uint32_t nchunks = (w + 31) / 32;
  if (nchunks == 0) nchunks = 1;
  size_t need = static_cast<size_t>(nchunks) * 8;
  if (cur.pos + need > cur.input.size()) return ScanFieldResult::kStop;
  auto vec = MakeLogic4VecVal(arena, w, 0);
  for (uint32_t k = 0; k < nchunks; ++k) {
    uint32_t off = k * 32;
    uint32_t mask = ScanChunkMask(w, off);
    size_t pair = cur.pos + static_cast<size_t>(k) * 8;
    uint64_t aval = ScanRead32(cur, pair) & mask;
    uint64_t bval = ScanRead32(cur, pair + 4) & mask;
    uint32_t word = off / 64;
    if (word < vec.nwords) {
      vec.words[word].aval |= aval << (off % 64);
      vec.words[word].bval |= bval << (off % 64);
    }
  }
  cur.pos += need;
  if (var) {
    var->value = vec;
    var->NotifyWatchers();
  }
  return ScanFieldResult::kMatched;
}

bool IsScanStrengthUnknownValue(char c) {
  return c == 'x' || c == 'X' || c == 'l' || c == 'L' || c == 'h' || c == 'H';
}

ScanFieldResult ScanStrengthField(ScanCursor cur, Variable* var, Arena& arena) {
  if (cur.pos + 3 > cur.input.size()) return ScanFieldResult::kStop;
  for (int k = 0; k < 3; ++k) {
    if (IsScanSpace(cur.input[cur.pos + k])) return ScanFieldResult::kStop;
  }
  char vc = cur.input[cur.pos + 2];
  bool a = false, b = false;
  if (vc == '1') {
    a = true;
  } else if (IsScanStrengthUnknownValue(vc)) {
    a = b = true;
  } else if (vc == 'z' || vc == 'Z') {
    b = true;
  } else if (vc != '0') {
    return ScanFieldResult::kStop;
  }
  cur.pos += 3;
  if (var) {
    auto vec = MakeLogic4VecVal(arena, var->value.width, 0);
    if (a) vec.words[0].aval |= 1;
    if (b) vec.words[0].bval |= 1;
    var->value = vec;
    var->NotifyWatchers();
  }
  return ScanFieldResult::kMatched;
}

int ScanDigitValue(char c, int base) {
  if (c >= '0' && c <= '9') {
    int v = c - '0';
    return v < base ? v : -1;
  }
  if (base == 16) {
    if (c >= 'a' && c <= 'f') return c - 'a' + 10;
    if (c >= 'A' && c <= 'F') return c - 'A' + 10;
  }
  return -1;
}

bool ScanIsXZDigit(char c) {
  return c == 'x' || c == 'X' || c == 'z' || c == 'Z' || c == '?';
}

struct ScanDigit {
  int val = 0;
  bool is_x = false;
  bool is_z = false;
};

void WriteScannedDigitBits(const ScanDigit& d, uint32_t base,
                           uint32_t bits_per_digit, Logic4Vec& vec) {
  for (uint32_t b = 0; b < bits_per_digit; ++b) {
    uint32_t bit = base + b;
    if (bit >= vec.width) return;
    bool a = d.is_x || (!d.is_z && (((d.val >> b) & 1) != 0));
    bool bb = d.is_x || d.is_z;
    if (a) vec.words[bit / 64].aval |= uint64_t{1} << (bit % 64);
    if (bb) vec.words[bit / 64].bval |= uint64_t{1} << (bit % 64);
  }
}

void StoreScannedDigits(Variable* var, const std::vector<ScanDigit>& digits,
                        uint32_t bits_per_digit, Arena& arena) {
  if (!var) return;
  uint32_t w = var->value.width;
  auto vec = MakeLogic4VecVal(arena, w, 0);
  for (size_t i = 0; i < digits.size(); ++i) {
    const ScanDigit& d = digits[digits.size() - 1 - i];
    WriteScannedDigitBits(d, static_cast<uint32_t>(i) * bits_per_digit,
                          bits_per_digit, vec);
  }
  var->value = vec;
  var->NotifyWatchers();
}

void StoreAllXZ(Variable* var, bool is_x, Arena& arena) {
  if (!var) return;
  uint32_t w = var->value.width;
  auto vec = MakeLogic4VecVal(arena, w, 0);
  for (uint32_t bit = 0; bit < w; ++bit) {
    if (is_x) vec.words[bit / 64].aval |= uint64_t{1} << (bit % 64);
    vec.words[bit / 64].bval |= uint64_t{1} << (bit % 64);
  }
  var->value = vec;
  var->NotifyWatchers();
}

bool ScanDecimalDigits(const ScanCursor& cur, size_t limit, size_t& p,
                       uint64_t& mag) {
  bool any = false;
  while (p < limit) {
    char c = cur.input[p];
    if (c == '_' && any) {
      ++p;
      continue;
    }
    if (c < '0' || c > '9') break;
    mag = mag * 10 + static_cast<uint64_t>(c - '0');
    any = true;
    ++p;
  }
  return any;
}

ScanFieldResult ScanDecimalField(ScanCursor cur, int width, Variable* var,
                                 Arena& arena) {
  size_t limit = ScanUpperLimit(cur, width);
  size_t p = cur.pos;
  bool neg = false;
  if (p < limit && (cur.input[p] == '+' || cur.input[p] == '-')) {
    neg = cur.input[p] == '-';
    ++p;
  }
  if (p < limit && ScanIsXZDigit(cur.input[p])) {
    char c = cur.input[p];
    cur.pos = p + 1;
    StoreAllXZ(var, c == 'x' || c == 'X', arena);
    return ScanFieldResult::kMatched;
  }
  uint64_t mag = 0;
  if (!ScanDecimalDigits(cur, limit, p, mag)) return ScanFieldResult::kStop;
  cur.pos = p;
  if (var) {
    uint64_t v = neg ? (0 - mag) : mag;
    var->value = MakeLogic4VecVal(arena, var->value.width, v);
    var->NotifyWatchers();
  }
  return ScanFieldResult::kMatched;
}

ScanFieldResult ScanIntegerField(ScanCursor cur, int base, int width,
                                 Variable* var, Arena& arena) {
  if (base == 10) return ScanDecimalField(cur, width, var, arena);
  size_t limit = ScanUpperLimit(cur, width);
  size_t p = cur.pos;
  std::vector<ScanDigit> digits;
  while (p < limit) {
    char c = cur.input[p];
    if (c == '_' && !digits.empty()) {
      ++p;
      continue;
    }
    int dv = ScanDigitValue(c, base);
    if (dv >= 0) {
      digits.push_back({dv, false, false});
      ++p;
      continue;
    }
    if (ScanIsXZDigit(c)) {
      digits.push_back({0, c == 'x' || c == 'X', c != 'x' && c != 'X'});
      ++p;
      continue;
    }
    break;
  }
  if (digits.empty()) return ScanFieldResult::kStop;
  cur.pos = p;
  uint32_t bits_per_digit = base == 2 ? 1 : (base == 8 ? 3 : 4);
  StoreScannedDigits(var, digits, bits_per_digit, arena);
  return ScanFieldResult::kMatched;
}

struct ScanSpec {
  bool stop = false;
  bool suppress = false;
  int width = 0;
  char code = '\0';
};

ScanSpec ParseScanSpec(const std::string& fmt, size_t& fi) {
  ScanSpec spec;
  if (fmt[fi] == '*') {
    spec.suppress = true;
    if (++fi >= fmt.size()) {
      spec.stop = true;
      return spec;
    }
  }
  while (fi < fmt.size() && fmt[fi] >= '0' && fmt[fi] <= '9') {
    spec.width = spec.width * 10 + (fmt[fi] - '0');
    ++fi;
  }
  if (fi >= fmt.size()) {
    spec.stop = true;
    return spec;
  }
  spec.code = fmt[fi];
  return spec;
}

struct ScanArgs {
  Expr* const* dest;
  size_t ndest;
  SimContext& ctx;
  SourceLoc loc;
  size_t ai = 0;
  uint32_t matched = 0;
  bool hit_end = false;
};

ScanDest StandInScanDest(const Expr* a, ScanArgs& args) {
  ScanDest d;
  Logic4Vec held = EvalExpr(a, args.ctx, args.ctx.GetArena());
  d.var = args.ctx.GetArena().Create<Variable>();
  d.var->value = held;
  d.is_string = held.is_string || NamesStringProperty(a, args.ctx);
  d.assign_back = a;
  return d;
}

ScanDest ResolveScanDest(ScanArgs& args, bool suppress) {
  ScanDest d;
  if (suppress || args.ai >= args.ndest) return d;
  const Expr* a = args.dest[args.ai];
  if (a == nullptr) return d;
  if (a->kind != ExprKind::kIdentifier) return StandInScanDest(a, args);
  d.name = a->text;
  const ArrayInfo* ai = args.ctx.FindArrayInfo(a->text);
  if (ai != nullptr) {
    if (!ai->is_dynamic && !ai->is_queue &&
        ai->elem_type_kind == DataTypeKind::kByte) {
      d.byte_array = ai;
    }
    return d;
  }
  d.var = args.ctx.FindVariable(a->text);
  if (d.var == nullptr) return StandInScanDest(a, args);
  d.is_string = args.ctx.IsStringVariable(a->text);
  return d;
}

void AssignScanStandIn(const ScanDest& dst, SimContext& ctx, Arena& arena) {
  if (dst.assign_back == nullptr || dst.var == nullptr) return;
  Logic4Vec value = dst.var->value;
  value.is_string = dst.is_string;
  PerformBlockingAssign(dst.assign_back, value, ctx, arena);
}

bool IsIntegerClassCode(char lc) {
  return lc == 'h' || lc == 'x' || lc == 'd' || lc == 'o' || lc == 'b' ||
         lc == 'c' || lc == 'u' || lc == 'z';
}

void SkipScanInputSpace(const ScanCursor& cur, ScanArgs& args) {
  while (cur.pos < cur.input.size() && IsScanSpace(cur.input[cur.pos]))
    ++cur.pos;
  if (cur.pos >= cur.input.size()) args.hit_end = true;
}

bool MatchScanLiteralChar(const ScanCursor& cur, char fc, ScanArgs& args) {
  if (cur.pos >= cur.input.size()) {
    args.hit_end = true;
    return false;
  }
  if (cur.input[cur.pos] != fc) return false;
  ++cur.pos;
  return true;
}

ScanFieldResult DispatchScanField(char lc, const ScanInputField& field,
                                  const ScanDest& dst, const ScanArgs& args,
                                  Arena& arena) {
  SimContext& ctx = args.ctx;
  const ScanCursor& cur = field.cur;
  int width = field.width;
  if (lc == 'c') {
    return ScanCharField(cur, width, dst, ctx, arena);
  }
  if (lc == 'm') {
    StoreScannedChars(dst,
                      FormatDisplay("%m", {}, {.ctx = &ctx, .loc = args.loc}),
                      ctx, arena);
    return ScanFieldResult::kMatched;
  }
  while (cur.pos < cur.input.size() && IsScanSpace(cur.input[cur.pos]))
    ++cur.pos;

  if (lc == 's') return ScanStringField(cur, width, dst, ctx, arena);
  if (lc == 'f' || lc == 'e' || lc == 'g' || lc == 't')
    return ScanRealField(field, lc == 't', dst.var, ctx, arena);
  if (lc == 'u') return ScanRawBinaryField(cur, dst.var, arena);
  if (lc == 'z') return ScanFourStateField(cur, dst.var, arena);
  if (lc == 'v') return ScanStrengthField(cur, dst.var, arena);
  int base = SpecToBase(lc);
  if (base == 0) return ScanFieldResult::kStop;
  return ScanIntegerField(cur, base, width, dst.var, arena);
}

bool RejectAggregateScanDest(char lc, const ScanSpec& spec, ScanArgs& args) {
  if (!IsIntegerClassCode(lc) || spec.suppress || args.ai >= args.ndest)
    return false;
  const Expr* a = args.dest[args.ai];
  if (ClassifyUnpackedAggregate(a, args.ctx) == UnpackedAggregateKind::kNone)
    return false;
  args.ctx.GetDiag().Warning(a->range.start,
                             std::string("$fscanf/$sscanf: %") + spec.code +
                                 " may not read into unpacked aggregate '" +
                                 std::string(a->text) + "'",
                             Subclause("21.3.4.3"));
  return true;
}

struct ScanOutcome {
  size_t start_pos;
  ScanFieldResult result;
};

void NoteScanEndOfInput(char lc, const ScanSpec& spec,
                        const ScanInputField& field, const ScanOutcome& done,
                        ScanArgs& args) {
  const ScanCursor& cur = field.cur;
  if (lc == 'c') {
    size_t want = spec.width > 0 ? static_cast<size_t>(spec.width) : 1;
    if (cur.pos >= cur.input.size() && cur.pos - done.start_pos < want)
      args.hit_end = true;
    return;
  }
  if (lc == 'u' || lc == 'z') {
    if (done.result == ScanFieldResult::kStop) args.hit_end = true;
    return;
  }
  if (lc != 'm' && cur.pos >= cur.input.size()) args.hit_end = true;
}

bool HandleScanSpecifier(const std::string& fmt, size_t& fi,
                         const ScanCursor& cur, ScanArgs& args, Arena& arena) {
  if (fi + 1 >= fmt.size()) return false;
  ++fi;
  ScanSpec spec = ParseScanSpec(fmt, fi);
  if (spec.stop) return false;
  char lc = (spec.code >= 'A' && spec.code <= 'Z')
                ? static_cast<char>(spec.code - 'A' + 'a')
                : spec.code;

  if (lc == '%') return MatchScanLiteralChar(cur, '%', args);
  if (RejectAggregateScanDest(lc, spec, args)) return false;

  ScanDest dst = ResolveScanDest(args, spec.suppress);
  size_t before = cur.pos;
  ScanFieldResult result =
      DispatchScanField(lc, {cur, spec.width}, dst, args, arena);
  NoteScanEndOfInput(lc, spec, {cur, spec.width}, {before, result}, args);
  if (result == ScanFieldResult::kMatched)
    AssignScanStandIn(dst, args.ctx, arena);

  if (result == ScanFieldResult::kStop) return false;
  if (result == ScanFieldResult::kMatched && !spec.suppress) {
    ++args.matched;
    ++args.ai;
  }
  return true;
}
}  // namespace

uint32_t RunScanf(const ScanRequest& req, SimContext& ctx, Arena& arena) {
  const std::string& input = req.input;
  const std::string& fmt = req.fmt;
  size_t pos = 0;
  ScanCursor cur{input, pos};
  ScanArgs args{req.dest, req.ndest, ctx, req.loc};

  for (size_t fi = 0; fi < fmt.size(); ++fi) {
    char fc = fmt[fi];

    if (IsScanSpace(fc)) {
      SkipScanInputSpace(cur, args);
      continue;
    }

    if (fc != '%') {
      if (!MatchScanLiteralChar(cur, fc, args)) break;
      continue;
    }

    if (!HandleScanSpecifier(fmt, fi, cur, args, arena)) break;
  }

  req.consumed = pos;
  if (req.hit_end != nullptr) *req.hit_end = args.hit_end;
  return args.matched;
}

static bool ReadByteArrayText(std::string_view name, SimContext& ctx,
                              std::string& out) {
  const ArrayInfo* ai = ctx.FindArrayInfo(name);
  if (ai == nullptr || ai->is_dynamic || ai->is_queue ||
      ai->elem_type_kind != DataTypeKind::kByte)
    return false;
  for (uint32_t i = 0; i < ai->size; ++i) {
    uint32_t idx =
        ai->is_descending ? (ai->lo + ai->size - 1 - i) : (ai->lo + i);
    std::string ename = std::string(name) + "[" + std::to_string(idx) + "]";
    Variable* elem = ctx.FindVariable(ename);
    char c = elem ? static_cast<char>(elem->value.ToUint64() & 0xFF) : '\0';
    out += c != 0 ? c : ' ';
  }
  return true;
}

static std::string PackedBytesToScanText(const Logic4Vec& val) {
  uint32_t nbytes = val.width / 8;
  std::string result;
  bool started = false;
  for (uint32_t i = nbytes; i > 0; --i) {
    uint32_t byte_idx = i - 1;
    uint32_t word = (byte_idx * 8) / 64;
    uint32_t bit = (byte_idx * 8) % 64;
    if (word >= val.nwords) continue;
    auto ch = static_cast<char>((val.words[word].aval >> bit) & 0xFF);
    if (!started && ch == 0) continue;
    started = true;
    result += ch != 0 ? ch : ' ';
  }
  return result;
}

static std::string DecodeSscanfInput(const Expr* arg, SimContext& ctx,
                                     Arena& arena) {
  if (arg->kind == ExprKind::kStringLiteral) return ExtractStrArg(arg);
  if (arg->kind == ExprKind::kIdentifier) {
    std::string s;
    if (ReadByteArrayText(arg->text, ctx, s)) return s;
  }
  return PackedBytesToScanText(EvalExpr(arg, ctx, arena));
}

Logic4Vec EvalSscanf(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.size() < 3) return MakeLogic4VecVal(arena, 32, 0);

  if (ScanArgHasUnknownBits(expr->args[0], ctx, arena) ||
      ScanArgHasUnknownBits(expr->args[1], ctx, arena)) {
    return MakeLogic4VecVal(arena, 32, 0xFFFFFFFF);
  }

  std::string input = DecodeSscanfInput(expr->args[0], ctx, arena);
  std::string fmt = ResolveFormatArg(expr->args[1], ctx, arena);

  size_t consumed = 0;
  ScanRequest req{input,
                  fmt,
                  expr->args.data() + 2,
                  expr->args.size() - 2,
                  consumed,
                  expr->range.start};
  uint32_t matched = RunScanf(req, ctx, arena);

  if (matched == 0) {
    size_t p = consumed;
    while (p < input.size() && IsScanSpace(input[p])) ++p;
    if (p >= input.size()) return MakeLogic4VecVal(arena, 32, 0xFFFFFFFF);
  }
  return MakeLogic4VecVal(arena, 32, matched);
}

}  // namespace delta
