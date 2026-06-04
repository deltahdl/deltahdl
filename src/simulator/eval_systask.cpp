#include <bit>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <iostream>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "parser/ast.h"
#include "simulator/class_object.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

namespace delta {

static uint32_t CountOnesInVec(const Logic4Vec& val) {
  uint32_t count = 0;
  for (uint32_t i = 0; i < val.nwords; ++i) {

    uint64_t known_ones = val.words[i].aval & ~val.words[i].bval;
    count += static_cast<uint32_t>(std::popcount(known_ones));
  }
  return count;
}

static Logic4Vec EvalClog2(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 32, 0);
  uint64_t v = EvalExpr(expr->args[0], ctx, arena).ToUint64();
  if (v <= 1) return MakeLogic4VecVal(arena, 32, 0);
  int result = 0;
  uint64_t shifted = v - 1;
  while (shifted > 0) {
    shifted >>= 1;
    ++result;
  }
  return MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(result));
}

static Logic4Vec EvalBits(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 32, 0);

  auto* arg = expr->args[0];
  if (arg->kind == ExprKind::kIdentifier) {
    uint32_t tw = ctx.FindTypeWidth(arg->text);
    if (tw > 0) return MakeLogic4VecVal(arena, 32, tw);
  }
  auto val = EvalExpr(arg, ctx, arena);
  return MakeLogic4VecVal(arena, 32, val.width);
}

static Logic4Vec EvalSignCast(const Expr* expr, SimContext& ctx, Arena& arena,
                              bool make_signed) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 32, 0);
  auto val = EvalExpr(expr->args[0], ctx, arena);
  val.is_signed = make_signed;
  return val;
}

static Logic4Vec EvalCountones(const Expr* expr, SimContext& ctx,
                               Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 32, 0);
  auto val = EvalExpr(expr->args[0], ctx, arena);
  return MakeLogic4VecVal(arena, 32, CountOnesInVec(val));
}

static Logic4Vec EvalOnehot(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 1, 0);
  auto val = EvalExpr(expr->args[0], ctx, arena);
  uint64_t result = (CountOnesInVec(val) == 1) ? 1 : 0;
  return MakeLogic4VecVal(arena, 1, result);
}

static Logic4Vec EvalOnehot0(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 1, 1);
  auto val = EvalExpr(expr->args[0], ctx, arena);
  uint64_t result = (CountOnesInVec(val) <= 1) ? 1 : 0;
  return MakeLogic4VecVal(arena, 1, result);
}

static Logic4Vec EvalIsunknown(const Expr* expr, SimContext& ctx,
                               Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 1, 0);
  auto val = EvalExpr(expr->args[0], ctx, arena);
  return MakeLogic4VecVal(arena, 1, HasUnknownBits(val) ? 1 : 0);
}

static std::string ExtractStrArg(const Expr* arg) {
  auto text = arg->text;
  if (text.size() >= 2 && text.front() == '"') {
    return std::string(text.substr(1, text.size() - 2));
  }
  return std::string(text);
}

static Logic4Vec EvalTestPlusargs(const Expr* expr, SimContext& ctx,
                                  Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 1, 0);
  std::string prefix = ExtractStrArg(expr->args[0]);
  for (const auto& arg : ctx.GetPlusArgs()) {
    if (arg.substr(0, prefix.size()) == prefix) {
      return MakeLogic4VecVal(arena, 1, 1);
    }
  }
  return MakeLogic4VecVal(arena, 1, 0);
}

static Logic4Vec EvalValuePlusargs(const Expr* expr, SimContext& ctx,
                                   Arena& arena) {
  if (expr->args.size() < 2) return MakeLogic4VecVal(arena, 1, 0);
  std::string pattern = ExtractStrArg(expr->args[0]);

  auto pct_pos = pattern.find('%');
  std::string prefix =
      (pct_pos != std::string::npos) ? pattern.substr(0, pct_pos) : pattern;

  for (const auto& arg : ctx.GetPlusArgs()) {
    if (arg.substr(0, prefix.size()) != prefix) continue;
    std::string value_str = arg.substr(prefix.size());

    if (!value_str.empty() && value_str[0] == '=') {
      value_str = value_str.substr(1);
    }
    uint64_t parsed_val = std::strtoull(value_str.c_str(), nullptr, 10);

    if (expr->args[1]->kind == ExprKind::kIdentifier) {
      auto* var = ctx.FindVariable(expr->args[1]->text);
      if (var)
        var->value = MakeLogic4VecVal(arena, var->value.width, parsed_val);
    }
    return MakeLogic4VecVal(arena, 1, 1);
  }
  return MakeLogic4VecVal(arena, 1, 0);
}

static std::string TypenameForVariable(const Variable* var) {
  uint32_t w = var->width;

  if (!var->is_4state && var->is_signed && w == 32) return "int";
  std::string base = var->is_4state ? "logic" : "bit";
  if (w <= 1) return base;
  return base + "[" + std::to_string(w - 1) + ":0]";
}

static Logic4Vec EvalTypename(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) {
    return StringToLogic4Vec(arena, "logic");
  }
  const auto* arg = expr->args[0];

  if (arg->kind == ExprKind::kIdentifier) {
    if (const auto* var = ctx.FindVariable(arg->text)) {
      return StringToLogic4Vec(arena, TypenameForVariable(var));
    }
  }
  return StringToLogic4Vec(arena, "logic");
}

// §21.3.3: the format argument may be a string literal or an expression whose
// content is interpreted as the formatting string. Literal forms are taken
// verbatim from the token text; non-literal forms have their packed-byte value
// decoded back into a std::string here.
static std::string ResolveFormatArg(const Expr* arg, SimContext& ctx,
                                    Arena& arena);

// §21.3.3: counts %-introduced specifiers that consume an argument value,
// excluding %% literals and %m/%l self-supplied specifiers.
static size_t CountConsumingSpecifiers(const std::string& fmt) {
  size_t n = 0;
  for (size_t i = 0; i + 1 < fmt.size(); ++i) {
    if (fmt[i] != '%') continue;
    char c = fmt[i + 1];
    if (c == '%') {
      ++i;
      continue;
    }
    size_t j = i + 1;
    while (j < fmt.size() && fmt[j] >= '0' && fmt[j] <= '9') ++j;
    if (j >= fmt.size()) break;
    char spec = fmt[j];
    if (spec >= 'A' && spec <= 'Z') spec = static_cast<char>(spec - 'A' + 'a');
    if (spec != 'm' && spec != 'l') ++n;
    i = j;
  }
  return n;
}

// §21.3.3 N14: when the supplied argument count does not match the number of
// consuming format specifiers, the application shall issue a warning and
// continue execution.
static void WarnIfArgCountMismatch(SimContext& ctx, std::string_view task_name,
                                   const std::string& fmt, size_t supplied) {
  size_t required = CountConsumingSpecifiers(fmt);
  if (supplied == required) return;
  std::string msg = std::string(task_name) +
                    ": format-specifier count (" + std::to_string(required) +
                    ") does not match supplied argument count (" +
                    std::to_string(supplied) + ")";
  ctx.GetDiag().Warning({}, std::move(msg));
}

static Logic4Vec EvalSformatf(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return StringToLogic4Vec(arena, "");
  // §21.3.3 N10: accept a string literal or any integral / byte-array /
  // string-typed expression as the format argument.
  std::string fmt = ResolveFormatArg(expr->args[0], ctx, arena);
  std::vector<Logic4Vec> arg_vals;
  for (size_t i = 1; i < expr->args.size(); ++i) {
    arg_vals.push_back(EvalExpr(expr->args[i], ctx, arena));
  }
  WarnIfArgCountMismatch(ctx, "$sformatf", fmt, arg_vals.size());
  std::string result = FormatDisplay(fmt, arg_vals);
  return StringToLogic4Vec(arena, result);
}

// §21.3.3: shared output-string builder used by $swrite{,b,h,o} and $sformat.
// `args` are the unevaluated argument expressions following the output
// variable; `default_radix` is the format-specifier letter applied to any
// bare expression argument when no embedded format string drives it.
static std::string BuildStringTaskOutput(const std::vector<Expr*>& args,
                                         char default_radix, SimContext& ctx,
                                         Arena& arena) {
  std::string out;
  for (size_t i = 0; i < args.size(); ++i) {
    const Expr* a = args[i];
    if (a == nullptr) {
      out += ' ';
      continue;
    }
    if (a->kind == ExprKind::kStringLiteral) {
      std::string fmt = ExtractFormatString(a);
      std::vector<Logic4Vec> vals;
      while (i + 1 < args.size() && args[i + 1] != nullptr &&
             args[i + 1]->kind != ExprKind::kStringLiteral) {
        vals.push_back(EvalExpr(args[++i], ctx, arena));
      }
      out += FormatDisplay(fmt, vals);
      continue;
    }
    auto val = EvalExpr(a, ctx, arena);
    char spec = val.is_string ? 's' : default_radix;
    char fmt_buf[3] = {'%', spec, 0};
    out += FormatDisplay(fmt_buf, {val});
  }
  return out;
}

// §21.3.3 N6: $swrite/$swriteb/$swriteh/$swriteo take an output variable as
// the first argument and write the formatted result into it under string-
// literal assignment-to-variable rules. The b/h/o suffix selects the default
// radix for bare expression arguments per §21.3.2.
static Logic4Vec EvalSwriteFamily(const Expr* expr, SimContext& ctx,
                                  Arena& arena, std::string_view name) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 1, 0);
  Variable* dst = nullptr;
  if (expr->args[0] && expr->args[0]->kind == ExprKind::kIdentifier) {
    dst = ctx.FindVariable(expr->args[0]->text);
  }

  // The suffix character ('\0' / b / h / o) becomes the default radix letter
  // for bare expression arguments. Without a suffix, decimal is the default.
  char default_radix = 'd';
  if (name.size() >= 1) {
    char back = name.back();
    if (back == 'b' || back == 'h' || back == 'o') default_radix = back;
  }

  std::vector<Expr*> rest(expr->args.begin() + 1, expr->args.end());
  std::string output =
      BuildStringTaskOutput(rest, default_radix, ctx, arena);
  if (dst) {
    // §5.9 / §21.3.3 N7: writing via StringToLogic4Vec packs the leftmost
    // character at the high byte position, giving left-bound to right-bound
    // ordering across the destination's bits.
    dst->value = StringToLogic4Vec(arena, output);
  }
  return MakeLogic4VecVal(arena, 1, 0);
}

// §21.3.3 N9: $sformat always interprets its second argument, and only its
// second argument, as the format string; following arguments fill its
// specifiers in order and are never re-interpreted as format strings.
static Logic4Vec EvalSformatTask(const Expr* expr, SimContext& ctx,
                                 Arena& arena) {
  if (expr->args.size() < 2) return MakeLogic4VecVal(arena, 1, 0);
  Variable* dst = nullptr;
  if (expr->args[0] && expr->args[0]->kind == ExprKind::kIdentifier) {
    dst = ctx.FindVariable(expr->args[0]->text);
  }
  std::string fmt = ResolveFormatArg(expr->args[1], ctx, arena);
  std::vector<Logic4Vec> vals;
  for (size_t i = 2; i < expr->args.size(); ++i) {
    vals.push_back(EvalExpr(expr->args[i], ctx, arena));
  }
  WarnIfArgCountMismatch(ctx, "$sformat", fmt, vals.size());
  std::string out = FormatDisplay(fmt, vals);
  if (dst) dst->value = StringToLogic4Vec(arena, out);
  return MakeLogic4VecVal(arena, 1, 0);
}

static Logic4Vec EvalItor(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 64, 0);
  auto val = EvalExpr(expr->args[0], ctx, arena);
  auto d = static_cast<double>(static_cast<int64_t>(val.ToUint64()));
  uint64_t bits = 0;
  std::memcpy(&bits, &d, sizeof(double));
  return MakeLogic4VecVal(arena, 64, bits);
}

static Logic4Vec EvalRtoi(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 32, 0);
  auto val = EvalExpr(expr->args[0], ctx, arena);
  uint64_t raw_bits = val.ToUint64();
  double d = 0.0;
  std::memcpy(&d, &raw_bits, sizeof(double));
  auto truncated = static_cast<int64_t>(d);
  return MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(truncated));
}

static Logic4Vec EvalBitstoreal(const Expr* expr, SimContext& ctx,
                                Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 64, 0);
  auto val = EvalExpr(expr->args[0], ctx, arena);
  return MakeLogic4VecVal(arena, 64, val.ToUint64());
}

static Logic4Vec EvalRealtobits(const Expr* expr, SimContext& ctx,
                                Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 64, 0);
  auto val = EvalExpr(expr->args[0], ctx, arena);
  uint64_t raw_bits = val.ToUint64();

  if (expr->args[0]->kind == ExprKind::kRealLiteral) {
    double d = expr->args[0]->real_val;
    std::memcpy(&raw_bits, &d, sizeof(double));
  }
  return MakeLogic4VecVal(arena, 64, raw_bits);
}

static uint32_t CountMatchingBits(const Logic4Vec& val, const bool match[4]) {
  uint32_t count = 0;
  for (uint32_t i = 0; i < val.nwords; ++i) {
    uint64_t a = val.words[i].aval;
    uint64_t b = val.words[i].bval;
    if (match[1]) count += static_cast<uint32_t>(std::popcount(a & ~b));
    if (match[0]) count += static_cast<uint32_t>(std::popcount(~a & ~b));
    if (match[3]) count += static_cast<uint32_t>(std::popcount(a & b));
    if (match[2]) count += static_cast<uint32_t>(std::popcount(~a & b));
  }
  if (match[0] && val.width < val.nwords * 64) {
    count -= val.nwords * 64 - val.width;
  }
  return count;
}

static Logic4Vec EvalCountbits(const Expr* expr, SimContext& ctx,
                               Arena& arena) {
  if (expr->args.size() < 2) return MakeLogic4VecVal(arena, 32, 0);
  auto val = EvalExpr(expr->args[0], ctx, arena);
  bool match[4] = {};
  for (size_t i = 1; i < expr->args.size(); ++i) {
    auto pat = EvalExpr(expr->args[i], ctx, arena);
    uint64_t a = pat.nwords > 0 ? pat.words[0].aval & 1 : 0;
    uint64_t b = pat.nwords > 0 ? pat.words[0].bval & 1 : 0;
    match[a + b * 2] = true;
  }
  return MakeLogic4VecVal(arena, 32, CountMatchingBits(val, match));
}

// Build an all-x integer result. §20.7 calls for 'x whenever a query has no
// well-defined answer (a dimensionless first argument or an out-of-range
// dimension index).
static Logic4Vec MakeUnknownInt(Arena& arena, uint32_t width) {
  auto vec = MakeLogic4Vec(arena, width);
  uint64_t mask = (width < 64) ? ((uint64_t{1} << width) - 1) : ~uint64_t{0};
  if (vec.nwords > 0) {
    vec.words[0].aval = mask;
    vec.words[0].bval = mask;
  }
  return vec;
}

// Bounds of a single array dimension, as the array query functions report them.
struct QueryDimBounds {
  int64_t left = 0;
  int64_t right = 0;
  int64_t low = 0;
  int64_t high = 0;
  int64_t increment = 1;
  int64_t size = 0;
  bool low_high_unknown = false;  // $low/$high are 'x for an empty assoc array
};

Logic4Vec EvalArrayQuerySysCall(const Expr* expr, SimContext& ctx, Arena& arena,
                                std::string_view name) {
  const Expr* arg0 = expr->args.empty() ? nullptr : expr->args[0];

  // Classify the first argument's outermost (slowest varying) dimension.
  AssocArrayObject* assoc = nullptr;
  QueueObject* queue = nullptr;
  const ArrayInfo* arr = nullptr;
  if (arg0 && arg0->kind == ExprKind::kIdentifier) {
    assoc = ctx.FindAssocArray(arg0->text);
    queue = ctx.FindQueue(arg0->text);
    arr = ctx.FindArrayInfo(arg0->text);
  }
  bool dynamic_outer =
      queue != nullptr || (arr != nullptr && (arr->is_dynamic || arr->is_queue));
  bool has_unpacked = assoc != nullptr || queue != nullptr || arr != nullptr;

  // Width of the packed element dimension (the [n-1:0] of an integer type).
  uint32_t elem_width = 32;
  bool is_real = false;
  bool is_string = false;
  if (assoc) {
    elem_width = assoc->elem_width;
  } else if (queue) {
    elem_width = queue->elem_width;
  } else if (arr) {
    elem_width = arr->elem_width;
  } else if (arg0 && arg0->kind == ExprKind::kIdentifier &&
             ctx.IsStringVariable(arg0->text)) {
    // §20.7: a string is a nonarray type that is equivalent to a simple bit
    // vector, so it always contributes exactly one packed dimension regardless
    // of how many characters it currently holds.
    is_string = true;
  } else if (arg0) {
    auto val = EvalExpr(arg0, ctx, arena);
    elem_width = val.width;
    is_real = val.is_real;
  }

  // A simple bit-vector type (string included) contributes one packed
  // dimension; a real (or any other nonvector) type contributes none.
  uint32_t packed_dims = (is_string || (elem_width > 0 && !is_real)) ? 1 : 0;
  uint32_t unpacked_dims = has_unpacked ? 1 : 0;
  uint32_t total_dims = packed_dims + unpacked_dims;

  if (name == "$dimensions")
    return MakeLogic4VecVal(arena, 32, total_dims);
  if (name == "$unpacked_dimensions")
    return MakeLogic4VecVal(arena, 32, unpacked_dims);

  // §20.7: 'x when the first argument has no dimensions ($dimensions would be
  // 0) or when the optional dimension index is out of range.
  if (total_dims == 0) return MakeUnknownInt(arena, 32);
  uint32_t dim = 1;
  if (expr->args.size() > 1)
    dim = static_cast<uint32_t>(EvalExpr(expr->args[1], ctx, arena).ToUint64());
  if (dim < 1 || dim > total_dims) return MakeUnknownInt(arena, 32);

  // Dimension 1 is the slowest varying. When an unpacked dimension is present
  // it is dimension 1 and the packed element dimension (if any) is dimension 2;
  // otherwise the packed dimension is dimension 1.
  bool query_unpacked = has_unpacked && dim == 1;

  QueryDimBounds q;
  if (query_unpacked && assoc) {
    // Associative array dimension with an integral index type.
    uint32_t iw = assoc->index_width ? assoc->index_width : 32;
    q.left = 0;
    q.right = (iw >= 64) ? static_cast<int64_t>(~uint64_t{0})
                         : static_cast<int64_t>((uint64_t{1} << iw) - 1);
    q.increment = -1;
    q.size = assoc->Size();
    if (assoc->int_data.empty()) {
      q.low_high_unknown = true;
    } else {
      q.low = assoc->int_data.begin()->first;
      q.high = assoc->int_data.rbegin()->first;
    }
  } else if (query_unpacked && dynamic_outer) {
    // Queue or dynamic array dimension: indices run 0 .. size-1, descending.
    int64_t count =
        queue ? static_cast<int64_t>(queue->elements.size())
              : static_cast<int64_t>(arr ? arr->size : 0);
    q.left = 0;
    q.right = count - 1;  // -1 when the dimension is currently empty
    q.low = 0;
    q.high = count - 1;
    q.increment = -1;
    q.size = count;
  } else if (query_unpacked && arr) {
    // Fixed-size unpacked dimension with declared bounds.
    int64_t lo = arr->lo;
    int64_t hi = arr->lo + static_cast<int64_t>(arr->size) - 1;
    q.left = arr->is_descending ? hi : lo;
    q.right = arr->is_descending ? lo : hi;
    q.low = lo;
    q.high = hi;
    q.size = arr->size;
    q.increment = (q.left >= q.right) ? 1 : -1;
  } else {
    // Packed element dimension [elem_width-1 : 0].
    q.left = static_cast<int64_t>(elem_width) - 1;
    q.right = 0;
    q.low = 0;
    q.high = static_cast<int64_t>(elem_width) - 1;
    q.size = elem_width;
    q.increment = (q.left >= q.right) ? 1 : -1;
  }

  auto as_int = [&](int64_t v) {
    return MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(v));
  };
  if (name == "$left") return as_int(q.left);
  if (name == "$right") return as_int(q.right);
  if (name == "$increment") return as_int(q.increment);
  if (name == "$low")
    return q.low_high_unknown ? MakeUnknownInt(arena, 32) : as_int(q.low);
  if (name == "$high")
    return q.low_high_unknown ? MakeUnknownInt(arena, 32) : as_int(q.high);
  return as_int(q.size);  // $size
}

// §20.15.6 Table 20-11 status code values returned through the trailing
// `status` output argument of every stochastic-analysis queue task and
// function. Value 7 ("not enough memory, cannot create queue") is defined by
// the table but has no deterministic trigger in the model, so nothing emits
// it.
enum QueueStatus : uint64_t {
  kQOk = 0,                 // OK
  kQFullCannotAdd = 1,      // queue full, cannot add
  kQUndefinedId = 2,        // undefined q_id
  kQEmptyCannotRemove = 3,  // queue empty, cannot remove
  kQUnsupportedType = 4,    // unsupported queue type, cannot create
  kQNonPositiveLength = 5,  // specified length <= 0, cannot create
  kQDuplicateId = 6,        // duplicate q_id, cannot create
};

// Read an argument as a signed value, sign-extending from its own width so a
// negative max_length is recognized as such (Table 20-11 status 5 keys on
// length <= 0).
static int64_t QueueSignedArg(const Logic4Vec& v) {
  uint64_t raw = v.ToUint64();
  uint32_t w = v.width;
  if (w == 0 || w >= 64) return static_cast<int64_t>(raw);
  uint64_t sign_bit = 1ull << (w - 1);
  if (raw & sign_bit) raw |= ~((1ull << w) - 1);
  return static_cast<int64_t>(raw);
}

// §20.15.6: deliver the resolved status code into the queue task's `status`
// output argument, which every queue task and function returns.
static void WriteQueueStatus(const Expr* status_arg, uint64_t status,
                             SimContext& ctx, Arena& arena) {
  if (!status_arg || status_arg->kind != ExprKind::kIdentifier) return;
  auto* var = ctx.FindVariable(status_arg->text);
  if (var) var->value = MakeLogic4VecVal(arena, var->value.width, status);
}

// §20.15.3: write an integer value back through one of $q_remove's output
// arguments (job_id, inform_id), keeping the destination variable's own width.
static void WriteQueueOutput(const Expr* out_arg, uint64_t value,
                             SimContext& ctx, Arena& arena) {
  if (!out_arg || out_arg->kind != ExprKind::kIdentifier) return;
  auto* var = ctx.FindVariable(out_arg->text);
  if (var) var->value = MakeLogic4VecVal(arena, var->value.width, value);
}

// §20.15.6: resolve and report the Table 20-11 status code for each
// stochastic-analysis queue task/function. The queue type/capacity validated
// at $q_initialize and the occupancy tracked across $q_add/$q_remove supply
// the error conditions. $q_remove additionally returns its removed entry's
// job_id/inform_id outputs (§20.15.3), $q_full its fullness result (§20.15.4),
// and $q_exam its requested statistic (§20.15.5) through the q_stat_value
// output.
static Logic4Vec EvalStochasticQueue(const Expr* expr, SimContext& ctx,
                                     Arena& arena, std::string_view name) {
  auto& queues = ctx.StochasticQueues();
  const auto& args = expr->args;

  if (name == "$q_initialize") {
    if (args.size() < 4) return MakeLogic4VecVal(arena, 32, 0);
    uint64_t q_id = EvalExpr(args[0], ctx, arena).ToUint64();
    int64_t q_type = QueueSignedArg(EvalExpr(args[1], ctx, arena));
    int64_t max_length = QueueSignedArg(EvalExpr(args[2], ctx, arena));
    uint64_t status;
    if (q_type != 1 && q_type != 2) {
      status = kQUnsupportedType;
    } else if (max_length <= 0) {
      status = kQNonPositiveLength;
    } else if (queues.count(q_id)) {
      status = kQDuplicateId;
    } else {
      queues[q_id] = StochasticQueue{q_type, max_length, 0};
      status = kQOk;
    }
    WriteQueueStatus(args[3], status, ctx, arena);
    return MakeLogic4VecVal(arena, 32, status);
  }

  if (name == "$q_add") {
    if (args.size() < 4) return MakeLogic4VecVal(arena, 32, 0);
    uint64_t q_id = EvalExpr(args[0], ctx, arena).ToUint64();
    auto it = queues.find(q_id);
    uint64_t status;
    if (it == queues.end()) {
      status = kQUndefinedId;
    } else if (static_cast<int64_t>(it->second.count) >=
               it->second.max_length) {
      status = kQFullCannotAdd;
    } else {
      // Retain the entry's identifiers so §20.15.3 $q_remove can return them;
      // the inform_id holds whatever value $q_add was handed (its meaning is
      // user-defined).
      uint64_t job_id = EvalExpr(args[1], ctx, arena).ToUint64();
      uint64_t inform_id = EvalExpr(args[2], ctx, arena).ToUint64();
      // §20.15.5: stamp the arrival time and fold it into the queue's activity
      // statistics so $q_exam can report mean interarrival time, peak occupancy
      // and wait times.
      uint64_t now = ctx.CurrentTime().ticks;
      auto& q = it->second;
      q.entries.push_back(StochasticQueueEntry{job_id, inform_id, now});
      if (q.arrivals == 0) q.first_arrival_tick = now;
      q.last_arrival_tick = now;
      ++q.arrivals;
      ++q.count;
      if (q.count > q.max_count) q.max_count = q.count;
      status = kQOk;
    }
    WriteQueueStatus(args[3], status, ctx, arena);
    return MakeLogic4VecVal(arena, 32, status);
  }

  if (name == "$q_remove") {
    // §20.15.3 $q_remove(q_id, job_id, inform_id, status): take an entry off
    // the queue selected by q_id (an integer input) and report the removed
    // entry's identifiers through the job_id and inform_id outputs.
    if (args.size() < 4) return MakeLogic4VecVal(arena, 32, 0);
    uint64_t q_id = EvalExpr(args[0], ctx, arena).ToUint64();
    auto it = queues.find(q_id);
    uint64_t status;
    if (it == queues.end()) {
      status = kQUndefinedId;
    } else if (it->second.count == 0) {
      status = kQEmptyCannotRemove;
    } else {
      // Choose the entry per the discipline fixed at $q_initialize: q_type 2
      // (LIFO) returns the most recently added entry, otherwise q_type 1
      // (FIFO) returns the oldest. $q_add always appends to the back.
      auto& q = it->second;
      StochasticQueueEntry entry;
      if (q.q_type == 2) {
        entry = q.entries.back();
        q.entries.pop_back();
      } else {
        entry = q.entries.front();
        q.entries.pop_front();
      }
      --q.count;
      // §20.15.5: a removed entry's residence time completes a wait sample,
      // feeding the shortest-ever and average wait-time statistics reported by
      // $q_exam.
      uint64_t now = ctx.CurrentTime().ticks;
      uint64_t wait = now >= entry.arrival_tick ? now - entry.arrival_tick : 0;
      if (q.departures == 0 || wait < q.shortest_wait) q.shortest_wait = wait;
      q.total_wait += wait;
      ++q.departures;
      WriteQueueOutput(args[1], entry.job_id, ctx, arena);
      WriteQueueOutput(args[2], entry.inform_id, ctx, arena);
      status = kQOk;
    }
    WriteQueueStatus(args[3], status, ctx, arena);
    return MakeLogic4VecVal(arena, 32, status);
  }

  if (name == "$q_full") {
    // §20.15.4: $q_full checks whether the queue named by q_id has room for
    // another entry, returning 1 when it is full and 0 when it is not. A queue
    // is full once its occupancy reaches the capacity fixed at $q_initialize.
    // The trailing status reports the operation outcome (§20.15.6); the only
    // error condition that applies is an undefined q_id.
    if (args.size() < 2) return MakeLogic4VecVal(arena, 32, 0);
    uint64_t q_id = EvalExpr(args[0], ctx, arena).ToUint64();
    auto it = queues.find(q_id);
    WriteQueueStatus(args[1], it == queues.end() ? kQUndefinedId : kQOk, ctx,
                     arena);
    uint64_t full = (it != queues.end() &&
                     static_cast<int64_t>(it->second.count) >=
                         it->second.max_length)
                        ? 1u
                        : 0u;
    return MakeLogic4VecVal(arena, 32, full);
  }

  if (name == "$q_exam") {
    // §20.15.5 $q_exam(q_id, q_stat_code, q_stat_value, status): report a
    // statistic about activity on the queue named by q_id. The q_stat_code
    // selects which statistic is delivered through the q_stat_value output, per
    // Table 20-10. An undefined q_id is the only applicable error (§20.15.6).
    if (args.size() < 4) return MakeLogic4VecVal(arena, 32, 0);
    uint64_t q_id = EvalExpr(args[0], ctx, arena).ToUint64();
    auto it = queues.find(q_id);
    if (it == queues.end()) {
      WriteQueueStatus(args[3], kQUndefinedId, ctx, arena);
      return MakeLogic4VecVal(arena, 32, kQUndefinedId);
    }
    const auto& q = it->second;
    int64_t code = QueueSignedArg(EvalExpr(args[1], ctx, arena));
    uint64_t now = ctx.CurrentTime().ticks;
    uint64_t value = 0;
    switch (code) {
      case 1:  // Current queue length.
        value = q.count;
        break;
      case 2:  // Mean interarrival time: total span between the first and last
               // arrival divided by the number of gaps between arrivals.
        value = q.arrivals > 1
                    ? (q.last_arrival_tick - q.first_arrival_tick) /
                          (q.arrivals - 1)
                    : 0;
        break;
      case 3:  // Maximum queue length ever reached.
        value = q.max_count;
        break;
      case 4:  // Shortest wait time ever, across removed entries.
        value = q.departures ? q.shortest_wait : 0;
        break;
      case 5:  // Longest wait among entries still queued: the oldest entry is at
               // the front, as $q_add appends in arrival order.
        value = q.entries.empty()
                    ? 0
                    : (now >= q.entries.front().arrival_tick
                           ? now - q.entries.front().arrival_tick
                           : 0);
        break;
      case 6:  // Average wait time over removed entries.
        value = q.departures ? q.total_wait / q.departures : 0;
        break;
      default:
        value = 0;
        break;
    }
    WriteQueueOutput(args[2], value, ctx, arena);
    WriteQueueStatus(args[3], kQOk, ctx, arena);
    return MakeLogic4VecVal(arena, 32, kQOk);
  }

  return MakeLogic4VecVal(arena, 32, 0);
}

Logic4Vec EvalVerifSysCall(const Expr* expr, SimContext& ctx, Arena& arena,
                           std::string_view name) {

  if (name == "$sampled") {
    if (expr->args.empty()) return MakeLogic4VecVal(arena, 1, 0);
    return EvalExpr(expr->args[0], ctx, arena);
  }
  if (name == "$past") {
    if (expr->args.empty()) return MakeLogic4VecVal(arena, 32, 0);
    return EvalExpr(expr->args[0], ctx, arena);
  }
  if (name == "$rose" || name == "$fell" || name == "$stable" ||
      name == "$changed") {
    return MakeLogic4VecVal(arena, 1, 0);
  }

  // §16.9.4: $past_gclk(v) is defined as $past(v,,,@$global_clock) and
  // $future_gclk(v) is the value of v sampled at the next global clock tick;
  // both yield the (sampled) value of their argument.
  if (name == "$past_gclk" || name == "$future_gclk") {
    if (expr->args.empty()) return MakeLogic4VecVal(arena, 32, 0);
    return EvalExpr(expr->args[0], ctx, arena);
  }

  // §16.9.4: the global clocking value-change functions ($rose_gclk,
  // $fell_gclk, $stable_gclk, $changed_gclk and the future $rising_gclk,
  // $falling_gclk, $steady_gclk, $changing_gclk) each return a 1-bit Boolean.
  if (name.ends_with("_gclk")) {
    return MakeLogic4VecVal(arena, 1, 0);
  }

  if (name.starts_with("$assert")) return MakeLogic4VecVal(arena, 1, 0);

  if (name.starts_with("$coverage")) return MakeLogic4VecVal(arena, 32, 0);

  if (name.starts_with("$q_"))
    return EvalStochasticQueue(expr, ctx, arena, name);

  return MakeLogic4VecVal(arena, 32, 0);
}

static Logic4Vec EvalConversionSysCall(const Expr* expr, SimContext& ctx,
                                       Arena& arena, std::string_view name) {
  if (name == "$itor") return EvalItor(expr, ctx, arena);
  if (name == "$rtoi") return EvalRtoi(expr, ctx, arena);
  if (name == "$bitstoreal") return EvalBitstoreal(expr, ctx, arena);
  if (name == "$realtobits") return EvalRealtobits(expr, ctx, arena);
  if (name == "$shortrealtobits") {
    if (expr->args.empty()) return MakeLogic4VecVal(arena, 32, 0);
    auto val = EvalExpr(expr->args[0], ctx, arena);
    double d = 0.0;
    uint64_t bits = val.ToUint64();
    std::memcpy(&d, &bits, sizeof(double));
    auto f = static_cast<float>(d);
    uint32_t fbits = 0;
    std::memcpy(&fbits, &f, sizeof(float));
    return MakeLogic4VecVal(arena, 32, fbits);
  }
  if (name == "$bitstoshortreal") {
    if (expr->args.empty()) return MakeLogic4VecVal(arena, 64, 0);
    auto val = EvalExpr(expr->args[0], ctx, arena);
    auto fbits = static_cast<uint32_t>(val.ToUint64());
    float f = 0.0f;
    std::memcpy(&f, &fbits, sizeof(float));
    auto d = static_cast<double>(f);
    uint64_t dbits = 0;
    std::memcpy(&dbits, &d, sizeof(double));
    auto result = MakeLogic4VecVal(arena, 64, dbits);
    result.is_real = true;
    return result;
  }
  if (name == "$countbits") return EvalCountbits(expr, ctx, arena);
  return MakeLogic4VecVal(arena, 1, 0);
}

static Logic4Vec EvalIsunbounded(const Expr* expr, SimContext& ctx,
                                 Arena& arena) {
  if (!expr->args.empty() && expr->args[0]->kind == ExprKind::kIdentifier) {
    bool ub = ctx.IsUnboundedParam(expr->args[0]->text);
    return MakeLogic4VecVal(arena, 1, ub ? 1 : 0);
  }
  return MakeLogic4VecVal(arena, 1, 0);
}

static Logic4Vec CastAssignSuccess(std::string_view dest_name, uint64_t src_val,
                                   SimContext& ctx, Arena& arena) {
  auto* var = ctx.FindVariable(dest_name);
  if (var) var->value = MakeLogic4VecVal(arena, var->value.width, src_val);
  return MakeLogic4VecVal(arena, 32, 1);
}

static bool TryCastEnum(std::string_view dest_name, uint64_t src_val,
                        SimContext& ctx, Arena& arena, Logic4Vec& out) {
  auto* enum_info = ctx.GetVariableEnumType(dest_name);
  if (!enum_info) return false;
  for (const auto& m : enum_info->members) {
    if (m.value == src_val) {
      out = CastAssignSuccess(dest_name, src_val, ctx, arena);
      return true;
    }
  }
  out = MakeLogic4VecVal(arena, 32, 0);
  return true;
}

static bool AreCastCompatible(const ClassTypeInfo* a, const ClassTypeInfo* b) {
  return a->IsA(b) || b->IsA(a) || a->is_interface || b->is_interface;
}

static bool TryCastClassHandle(std::string_view dest_name, uint64_t src_val,
                               const Expr* src_expr, SimContext& ctx,
                               Arena& arena, Logic4Vec& out) {
  auto dest_class = ctx.GetVariableClassType(dest_name);
  if (dest_class.empty()) return false;
  auto* dest_type = ctx.FindClassType(dest_class);
  if (!dest_type) {
    out = MakeLogic4VecVal(arena, 32, 0);
    return true;
  }

  if (src_expr && src_expr->kind == ExprKind::kIdentifier &&
      src_expr->text != "null") {
    auto src_class = ctx.GetVariableClassType(src_expr->text);
    if (!src_class.empty()) {
      auto* src_type = ctx.FindClassType(src_class);
      if (src_type && !AreCastCompatible(src_type, dest_type)) {
        out = MakeLogic4VecVal(arena, 32, 0);
        return true;
      }
    }
  }

  if (src_val == kNullClassHandle) {
    out = CastAssignSuccess(dest_name, 0, ctx, arena);
    return true;
  }
  auto* src_obj = ctx.GetClassObject(src_val);
  if (!src_obj || !src_obj->type || !src_obj->type->IsA(dest_type)) {
    out = MakeLogic4VecVal(arena, 32, 0);
    return true;
  }
  out = CastAssignSuccess(dest_name, src_val, ctx, arena);
  return true;
}

static Logic4Vec EvalCastSysFunc(const Expr* expr, SimContext& ctx,
                                 Arena& arena) {
  if (expr->args.size() < 2 || !expr->args[0]) {
    return MakeLogic4VecVal(arena, 32, 0);
  }
  auto* dest_expr = expr->args[0];
  auto src = EvalExpr(expr->args[1], ctx, arena);
  uint64_t src_val = src.ToUint64();
  if (dest_expr->kind != ExprKind::kIdentifier) {
    return MakeLogic4VecVal(arena, 32, 0);
  }
  auto dest_name = dest_expr->text;
  Logic4Vec out;
  if (TryCastEnum(dest_name, src_val, ctx, arena, out)) return out;
  if (TryCastClassHandle(dest_name, src_val, expr->args[1], ctx, arena, out))
    return out;
  return CastAssignSuccess(dest_name, src_val, ctx, arena);
}

Logic4Vec EvalUtilitySysCall(const Expr* expr, SimContext& ctx, Arena& arena,
                             std::string_view name) {
  if (name == "$clog2") return EvalClog2(expr, ctx, arena);
  if (name == "$bits") return EvalBits(expr, ctx, arena);
  if (name == "$signed") return EvalSignCast(expr, ctx, arena, true);
  if (name == "$unsigned") return EvalSignCast(expr, ctx, arena, false);
  if (name == "$countones") return EvalCountones(expr, ctx, arena);
  if (name == "$onehot") return EvalOnehot(expr, ctx, arena);
  if (name == "$onehot0") return EvalOnehot0(expr, ctx, arena);
  if (name == "$isunknown") return EvalIsunknown(expr, ctx, arena);
  if (name == "$isunbounded") return EvalIsunbounded(expr, ctx, arena);
  if (name == "$cast") return EvalCastSysFunc(expr, ctx, arena);
  if (name == "$test$plusargs") return EvalTestPlusargs(expr, ctx, arena);
  if (name == "$value$plusargs") return EvalValuePlusargs(expr, ctx, arena);
  if (name == "$typename") return EvalTypename(expr, ctx, arena);
  if (name == "$sformatf") return EvalSformatf(expr, ctx, arena);
  return EvalConversionSysCall(expr, ctx, arena, name);
}

static std::string EvalStringArg(const Expr* arg, SimContext& ctx,
                                 Arena& arena);

static Logic4Vec EvalFopen(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 32, 0);
  // §21.3.1 admits a filename / type argument that is a string literal, a
  // string-typed variable, or an integral value whose bytes encode the
  // characters; EvalStringArg handles all three forms.
  std::string filename = EvalStringArg(expr->args[0], ctx, arena);
  // §21.3.1: omitting the type argument requests a multichannel descriptor;
  // supplying it requests a single 32-bit file descriptor.
  if (expr->args.size() < 2) {
    uint32_t mcd = ctx.OpenMcd(filename);
    return MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(mcd));
  }
  std::string mode = EvalStringArg(expr->args[1], ctx, arena);
  uint32_t fd = ctx.OpenFile(filename, mode);
  return MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(fd));
}

static Logic4Vec EvalFclose(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 1, 0);
  auto descriptor =
      static_cast<uint32_t>(EvalExpr(expr->args[0], ctx, arena).ToUint64());
  ctx.CloseFile(descriptor);
  return MakeLogic4VecVal(arena, 1, 0);
}

// Determines whether a system-task name names a §21.3.2 file-output task and,
// if so, returns the radix character for any base-specific suffix (b/h/o).
// Returns '\0' for the default ($fdisplay, $fwrite, $fstrobe, $fmonitor),
// 'b'/'h'/'o' for the suffixed variants, and '?' if the name is not in the set.
static char FileOutputSuffix(std::string_view name) {
  auto match = [&](std::string_view base) -> char {
    if (name == base) return '\0';
    if (name.size() == base.size() + 1 && name.substr(0, base.size()) == base) {
      char c = name.back();
      if (c == 'b' || c == 'h' || c == 'o') return c;
    }
    return '?';
  };
  for (auto base : {"$fdisplay", "$fwrite", "$fstrobe", "$fmonitor"}) {
    char s = match(base);
    if (s != '?') return s;
  }
  return '?';
}

static bool IsFileOutputTask(std::string_view name) {
  return FileOutputSuffix(name) != '?';
}

// Routes formatted output to every FILE* selected by a descriptor argument.
// An fd has its MSB set and refers to a single open file (or to STDIN/STDOUT/
// STDERR); an mcd has its MSB clear and may select multiple channels at once
// by setting their channel bits (§21.3.1, §21.3.2).
static std::vector<FILE*> ResolveOutputTargets(uint32_t descriptor,
                                               SimContext& ctx) {
  if ((descriptor & SimContext::kFdMsb) != 0) {
    FILE* fp = ctx.GetFileHandle(descriptor);
    if (fp == nullptr) return {};
    return {fp};
  }
  return ctx.GetMcdFiles(descriptor);
}

static Logic4Vec EvalFdisplayWrite(const Expr* expr, SimContext& ctx,
                                   Arena& arena, std::string_view name) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 1, 0);
  auto descriptor =
      static_cast<uint32_t>(EvalExpr(expr->args[0], ctx, arena).ToUint64());
  auto targets = ResolveOutputTargets(descriptor, ctx);
  if (targets.empty()) return MakeLogic4VecVal(arena, 1, 0);

  char suffix = FileOutputSuffix(name);
  bool is_display_family =
      name.rfind("$fdisplay", 0) == 0 || name.rfind("$fstrobe", 0) == 0 ||
      name.rfind("$fmonitor", 0) == 0;

  std::string fmt;
  std::vector<Logic4Vec> arg_vals;
  for (size_t i = 1; i < expr->args.size(); ++i) {
    auto val = EvalExpr(expr->args[i], ctx, arena);
    if (i == 1 && expr->args[i]->kind == ExprKind::kStringLiteral) {
      fmt = ExtractFormatString(expr->args[i]);
    } else {
      arg_vals.push_back(val);
    }
  }
  std::string output;
  if (!fmt.empty()) {
    output = FormatDisplay(fmt, arg_vals);
  } else if (suffix != '\0') {
    // §21.3.2 derives b/h/o radix from the task-name suffix when no format
    // string is supplied.
    char fmt_buf[3] = {'%', suffix, 0};
    output = FormatDisplay(fmt_buf, arg_vals);
  }
  for (FILE* fp : targets) {
    std::fputs(output.c_str(), fp);
    if (is_display_family) std::fputc('\n', fp);
    std::fflush(fp);
  }
  return MakeLogic4VecVal(arena, 1, 0);
}

static uint64_t ParseHexLine(const std::string& line) {
  return std::strtoull(line.c_str(), nullptr, 16);
}

static uint64_t ParseBinLine(const std::string& line) {
  return std::strtoull(line.c_str(), nullptr, 2);
}

static Logic4Vec EvalReadmem(const Expr* expr, SimContext& ctx, Arena& arena,
                             bool is_hex) {
  if (expr->args.size() < 2) return MakeLogic4VecVal(arena, 1, 0);
  std::string filename = ExtractStrArg(expr->args[0]);

  std::ifstream ifs(filename);
  if (!ifs.is_open()) {
    std::cerr << "WARNING: $readmem" << (is_hex ? "h" : "b")
              << ": cannot open file: " << filename << "\n";
    return MakeLogic4VecVal(arena, 1, 0);
  }

  Variable* target = nullptr;
  if (expr->args[1]->kind == ExprKind::kIdentifier) {
    target = ctx.FindVariable(expr->args[1]->text);
  }
  if (!target) return MakeLogic4VecVal(arena, 1, 0);

  std::string line;
  while (std::getline(ifs, line)) {

    if (line.empty() || line[0] == '/' || line[0] == '#') continue;
    uint64_t val = is_hex ? ParseHexLine(line) : ParseBinLine(line);
    target->value = MakeLogic4VecVal(arena, target->value.width, val);
    break;
  }
  return MakeLogic4VecVal(arena, 1, 0);
}

static Logic4Vec EvalWritemem(const Expr* expr, SimContext& ctx, Arena& arena,
                              bool is_hex) {
  if (expr->args.size() < 2) return MakeLogic4VecVal(arena, 1, 0);
  std::string filename = ExtractStrArg(expr->args[0]);

  Variable* target = nullptr;
  if (expr->args[1]->kind == ExprKind::kIdentifier) {
    target = ctx.FindVariable(expr->args[1]->text);
  }
  if (!target) return MakeLogic4VecVal(arena, 1, 0);

  std::ofstream ofs(filename);
  if (!ofs.is_open()) {
    std::cerr << "WARNING: $writemem" << (is_hex ? "h" : "b")
              << ": cannot open file: " << filename << "\n";
    return MakeLogic4VecVal(arena, 1, 0);
  }

  if (is_hex) {
    char buf[32];
    std::snprintf(buf, sizeof(buf), "%llx",
                  static_cast<unsigned long long>(target->value.ToUint64()));
    ofs << buf << "\n";
  } else {
    ofs << target->value.ToString() << "\n";
  }
  return MakeLogic4VecVal(arena, 1, 0);
}

static int SpecToBase(char spec) {
  if (spec == 'd') return 10;
  if (spec == 'h' || spec == 'x') return 16;
  if (spec == 'b') return 2;
  return 0;
}

struct ScanResult {
  uint64_t value = 0;
  size_t new_pos = 0;
  bool ok = false;
};

static ScanResult ScanOneValue(const std::string& input, size_t pos, int base) {
  ScanResult sr;
  while (pos < input.size() && input[pos] == ' ') ++pos;
  char* end = nullptr;
  sr.value = std::strtoull(input.c_str() + pos, &end, base);
  sr.ok = (end != input.c_str() + pos);
  sr.new_pos = sr.ok ? static_cast<size_t>(end - input.c_str()) : pos;
  return sr;
}

static std::string EvalStringArg(const Expr* arg, SimContext& ctx,
                                 Arena& arena) {
  if (arg->kind == ExprKind::kStringLiteral) return ExtractStrArg(arg);
  auto val = EvalExpr(arg, ctx, arena);
  uint32_t nbytes = val.width / 8;
  std::string result;
  for (uint32_t i = nbytes; i > 0; --i) {
    uint32_t byte_idx = i - 1;
    uint32_t word = (byte_idx * 8) / 64;
    uint32_t bit = (byte_idx * 8) % 64;
    if (word >= val.nwords) continue;
    auto ch = static_cast<char>((val.words[word].aval >> bit) & 0xFF);
    if (ch != 0) result += ch;
  }
  return result;
}

// §21.3.3 N10: a format argument may be supplied as a string literal or as
// any expression whose packed-byte value encodes the formatting string.
static std::string ResolveFormatArg(const Expr* arg, SimContext& ctx,
                                    Arena& arena) {
  if (arg && arg->kind == ExprKind::kStringLiteral) {
    return ExtractFormatString(arg);
  }
  return EvalStringArg(arg, ctx, arena);
}

static Logic4Vec EvalSscanf(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.size() < 3) return MakeLogic4VecVal(arena, 32, 0);
  std::string input = EvalStringArg(expr->args[0], ctx, arena);
  std::string fmt = ExtractStrArg(expr->args[1]);

  uint32_t matched = 0;
  size_t arg_idx = 2;
  size_t input_pos = 0;

  for (size_t fi = 0; fi < fmt.size(); ++fi) {
    if (fmt[fi] != '%' || fi + 1 >= fmt.size()) continue;
    int base = SpecToBase(fmt[++fi]);
    if (base == 0 || arg_idx >= expr->args.size()) break;

    auto sr = ScanOneValue(input, input_pos, base);
    if (!sr.ok) break;
    input_pos = sr.new_pos;

    if (expr->args[arg_idx]->kind == ExprKind::kIdentifier) {
      auto* var = ctx.FindVariable(expr->args[arg_idx]->text);
      if (var) var->value = MakeLogic4VecVal(arena, var->value.width, sr.value);
    }
    ++matched;
    ++arg_idx;
  }
  return MakeLogic4VecVal(arena, 32, matched);
}

Logic4Vec EvalIOSysCall(const Expr* expr, SimContext& ctx, Arena& arena,
                        std::string_view name) {
  if (name == "$fopen") return EvalFopen(expr, ctx, arena);
  if (name == "$fclose") return EvalFclose(expr, ctx, arena);
  if (IsFileOutputTask(name)) {
    return EvalFdisplayWrite(expr, ctx, arena, name);
  }
  if (name == "$readmemh") return EvalReadmem(expr, ctx, arena, true);
  if (name == "$readmemb") return EvalReadmem(expr, ctx, arena, false);
  if (name == "$writememh") return EvalWritemem(expr, ctx, arena, true);
  if (name == "$writememb") return EvalWritemem(expr, ctx, arena, false);
  if (name == "$sscanf") return EvalSscanf(expr, ctx, arena);
  // §21.3.3: the $swrite family and $sformat target a variable rather than a
  // file descriptor but otherwise mirror their $fwrite / $fdisplay
  // counterparts.
  if (name == "$swrite" || name == "$swriteb" || name == "$swriteh" ||
      name == "$swriteo") {
    return EvalSwriteFamily(expr, ctx, arena, name);
  }
  if (name == "$sformat") return EvalSformatTask(expr, ctx, arena);
  return MakeLogic4VecVal(arena, 1, 0);
}

}
