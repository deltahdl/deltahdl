#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <iterator>
#include <string>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "simulator/assoc_index.h"
#include "simulator/eval_class_array.h"
#include "simulator/eval_systask_internal.h"
#include "simulator/eval_systask_readmem_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/variable.h"

namespace delta {

struct ReadmemElemType {
  uint32_t elem_width;
  bool two_state;
  const EnumTypeInfo* enum_info;
};

struct MemSlice {
  bool is_slice;
  int64_t slice_lo;
  int64_t slice_hi;
};

template <class AddrFn, class WordFn>
bool DispatchMemFileToken(const std::string& tok, AddrFn& on_addr,
                          WordFn& on_word) {
  if (tok[0] == '@') {
    auto addr =
        static_cast<int64_t>(std::strtoull(tok.c_str() + 1, nullptr, 16));
    return on_addr(addr);
  }
  return on_word(tok);
}

template <class AddrFn, class WordFn>
bool ScanMemFile(const ReadmemEnv& env, const std::string& content,
                 AddrFn on_addr, WordFn on_word) {
  size_t pos = 0;
  size_t n = content.size();
  while (pos < n) {
    char c = content[pos];
    if (IsMemFileSpace(c)) {
      ++pos;
      continue;
    }
    if (SkipMemFileComment(content, n, pos)) continue;
    std::string tok = ScanMemFileToken(content, n, pos);
    if (tok.empty()) continue;
    if (!CheckMemFileToken(env, tok)) return false;
    if (!DispatchMemFileToken(tok, on_addr, on_word)) return false;
  }
  return true;
}

static bool ParseReadmemWord(const ReadmemEnv& env, const std::string& tok,
                             const ReadmemElemType& et, Logic4Vec& out) {
  out = ParseMemNumber(env.arena, tok, env.is_hex, et.elem_width);
  if (et.two_state) CoerceToTwoState(out);
  if (et.enum_info && !EnumValueInRange(et.enum_info, out)) {
    env.ctx.GetDiag().Error(env.loc,
                            "$readmem" + std::string(env.is_hex ? "h" : "b") +
                                ": value out of range for the enumerated type",
                            Subclause("21.4.2"));
    return false;
  }
  return true;
}

struct MemWindow {
  int64_t low_addr;
  int64_t high_addr;
  bool is_slice;
};

static bool CheckReadmemSliceBounds(const ReadmemEnv& env, const MemWindow& mw,
                                    const ReadmemWindow& w) {
  auto outside = [&](int64_t a) { return a < mw.low_addr || a > mw.high_addr; };
  if (mw.is_slice && w.has_start &&
      (outside(w.start_arg) || (w.has_finish && outside(w.finish_arg)))) {
    env.ctx.GetDiag().Error(
        env.loc,
        "$readmem" + std::string(env.is_hex ? "h" : "b") +
            ": start/finish address outside the slice bounds",
        Subclause("21.4"));
    return false;
  }
  return true;
}

struct TaskAddrRange {
  bool has_start;
  bool has_finish;
  int64_t task_lo;
  int64_t task_hi;
};

struct IndexedLoadState {
  int64_t cursor = 0;
  bool addr_in_file = false;
  uint64_t data_words = 0;
};

static void WarnReadmemWordCount(const ReadmemEnv& env,
                                 const TaskAddrRange& range,
                                 const IndexedLoadState& st) {
  if (range.has_start && range.has_finish && !st.addr_in_file) {
    auto span = static_cast<uint64_t>(range.task_hi - range.task_lo + 1);
    if (st.data_words != span) {
      env.ctx.GetDiag().Warning(
          env.loc,
          "$readmem" + std::string(env.is_hex ? "h" : "b") +
              ": number of data words differs from the address range",
          Subclause("21.4"));
    }
  }
}

static bool HandleIndexedAddr(const ReadmemEnv& env, const TaskAddrRange& range,
                              int64_t addr, IndexedLoadState& st) {
  st.addr_in_file = true;
  if (range.has_start && (addr < range.task_lo || addr > range.task_hi)) {
    env.ctx.GetDiag().Error(
        env.loc,
        "$readmem" + std::string(env.is_hex ? "h" : "b") +
            ": file address outside the range given by the task",
        Subclause("21.4"));
    return false;
  }
  st.cursor = addr;
  return true;
}

struct IndexedWordCtx {
  ReadmemElemType et;
  bool descending;
};

template <class WriteFn>
static bool HandleIndexedWord(const ReadmemEnv& env, const IndexedWordCtx& iwc,
                              const std::string& tok, WriteFn& write_word,
                              IndexedLoadState& st) {
  Logic4Vec word;
  if (!ParseReadmemWord(env, tok, iwc.et, word)) return false;
  write_word(st.cursor, word);
  ++st.data_words;
  st.cursor += iwc.descending ? -1 : 1;
  return true;
}

struct IndexedLoadReq {
  MemWindow mw;
  ReadmemElemType et;
  ReadmemWindow w;
};

template <class StoreFn>
static void EvalReadmemIndexed(const ReadmemEnv& env,
                               const std::string& content,
                               const IndexedLoadReq& req, StoreFn store) {
  const MemWindow& mw = req.mw;
  const ReadmemWindow& w = req.w;

  int64_t start_addr = w.has_start ? w.start_arg : mw.low_addr;
  int64_t finish_addr = w.has_finish ? w.finish_arg : mw.high_addr;

  bool descending = w.has_start && w.has_finish && start_addr > finish_addr;

  TaskAddrRange range;
  range.has_start = w.has_start;
  range.has_finish = w.has_finish;
  range.task_lo = w.has_finish ? std::min(start_addr, finish_addr) : start_addr;
  range.task_hi =
      w.has_finish ? std::max(start_addr, finish_addr) : mw.high_addr;

  ReadmemWindow resolved{w.has_start, w.has_finish, start_addr, finish_addr};
  if (!CheckReadmemSliceBounds(env, mw, resolved)) {
    return;
  }

  auto write_word = [&](int64_t addr, const Logic4Vec& v) {
    if (addr < mw.low_addr || addr > mw.high_addr) return;
    store(addr, v);
  };

  IndexedWordCtx iwc{req.et, descending};
  IndexedLoadState st;
  st.cursor = w.has_start ? start_addr : mw.low_addr;
  bool whole = ScanMemFile(
      env, content,
      [&](int64_t addr) -> bool {
        return HandleIndexedAddr(env, range, addr, st);
      },
      [&](const std::string& tok) -> bool {
        return HandleIndexedWord(env, iwc, tok, write_word, st);
      });

  if (whole) WarnReadmemWordCount(env, range, st);
}

static bool HandleAssocWord(const ReadmemEnv& env, const IndexedWordCtx& iwc,
                            AssocArrayObject* aa, const std::string& tok,
                            int64_t& cursor) {
  Logic4Vec word;
  if (!ParseReadmemWord(env, tok, iwc.et, word)) {
    return false;
  }
  aa->int_data[cursor] = word;
  cursor += iwc.descending ? -1 : 1;
  return true;
}

static void EvalReadmemAssoc(const ReadmemEnv& env, const std::string& content,
                             AssocArrayObject* aa, const ReadmemElemType& et,
                             const ReadmemWindow& w) {
  if (aa->is_string_key) {
    env.ctx.GetDiag().Error(
        env.loc,
        "$readmem" + std::string(env.is_hex ? "h" : "b") +
            ": associative array index must be of an integral type",
        Subclause("21.4.1"));
    return;
  }

  int64_t start_addr = w.has_start ? w.start_arg : 0;
  int64_t finish_addr = w.has_finish ? w.finish_arg : 0;
  bool descending = w.has_start && w.has_finish && start_addr > finish_addr;
  int64_t cursor = start_addr;

  IndexedWordCtx iwc{et, descending};
  ScanMemFile(
      env, content,
      [&](int64_t addr) -> bool {
        cursor = addr;
        return true;
      },
      [&](const std::string& tok) -> bool {
        return HandleAssocWord(env, iwc, aa, tok, cursor);
      });
}

struct MultiDimGeom {
  const std::string& mem_name;
  const std::vector<uint32_t>& los;
  const std::vector<uint32_t>& sizes;
  size_t ndim;
  uint64_t inner;
  int64_t top_lo;
  int64_t top_hi;
  uint64_t total;
};

static std::string MultiDimElementName(const MultiDimGeom& g, uint64_t global) {
  uint64_t top = global / g.inner;
  uint64_t flat = global % g.inner;
  std::string nm = g.mem_name + "[" +
                   std::to_string(static_cast<uint32_t>(
                       g.top_lo + static_cast<int64_t>(top))) +
                   "]";
  std::vector<uint32_t> subs(g.ndim - 1);
  for (size_t d = g.ndim - 1; d >= 1; --d) {
    subs[d - 1] = g.los[d] + static_cast<uint32_t>(flat % g.sizes[d]);
    flat /= g.sizes[d];
  }
  for (size_t d = 1; d < g.ndim; ++d) {
    nm += "[" + std::to_string(subs[d - 1]) + "]";
  }
  return nm;
}

static bool HandleMultiDimAddr(const ReadmemEnv& env, const MultiDimGeom& g,
                               int64_t addr, uint64_t& cursor) {
  if (addr < g.top_lo || addr > g.top_hi) {
    env.ctx.GetDiag().Error(
        env.loc,
        "$readmem" + std::string(env.is_hex ? "h" : "b") +
            ": file address outside the highest dimension's range",
        Subclause("21.4.3"));
    return false;
  }
  cursor = static_cast<uint64_t>(addr - g.top_lo) * g.inner;
  return true;
}

static bool HandleMultiDimWord(const ReadmemEnv& env, const MultiDimGeom& g,
                               const ReadmemElemType& et,
                               const std::string& tok, uint64_t& cursor) {
  if (cursor >= g.total) return false;
  Logic4Vec word;
  if (!ParseReadmemWord(env, tok, et, word)) {
    return false;
  }
  std::string elem = MultiDimElementName(g, cursor);
  if (auto* var = env.ctx.FindVariable(elem)) {
    var->value = word;
    var->NotifyWatchers();
  }
  ++cursor;
  return true;
}

static void EvalReadmemMultiDim(const ReadmemEnv& env,
                                const std::string& content,
                                const std::string& mem_name,
                                const ArrayInfo* ai,
                                const ReadmemElemType& et) {
  const std::vector<uint32_t>& los = ai->dim_los;
  const std::vector<uint32_t>& sizes = ai->dim_sizes;
  const size_t kNdim = sizes.size();

  uint64_t inner = 1;
  for (size_t d = 1; d < kNdim; ++d) inner *= sizes[d];
  if (inner == 0) return;

  const auto kTopLo = static_cast<int64_t>(los[0]);
  const int64_t kTopHi = kTopLo + static_cast<int64_t>(sizes[0]) - 1;
  const uint64_t kTotal = static_cast<uint64_t>(sizes[0]) * inner;

  MultiDimGeom geom{mem_name, los, sizes, kNdim, inner, kTopLo, kTopHi, kTotal};
  uint64_t cursor = 0;

  ScanMemFile(
      env, content,
      [&](int64_t addr) -> bool {
        return HandleMultiDimAddr(env, geom, addr, cursor);
      },
      [&](const std::string& tok) -> bool {
        return HandleMultiDimWord(env, geom, et, tok, cursor);
      });
}

struct MemSubscript {
  bool is_slice;
  int64_t a;
  int64_t b;
};

static bool CollectMemSubscripts(const ReadmemEnv& env, const Expr* mn,
                                 std::string& base_name,
                                 std::vector<MemSubscript>& subs) {
  std::vector<MemSubscript> rev;
  const Expr* e = mn;
  while (e != nullptr && e->kind == ExprKind::kSelect &&
         !e->is_part_select_plus && !e->is_part_select_minus &&
         e->base != nullptr) {
    int64_t a =
        static_cast<int64_t>(EvalExpr(e->index, env.ctx, env.arena).ToUint64());
    if (e->index_end != nullptr) {
      int64_t b = static_cast<int64_t>(
          EvalExpr(e->index_end, env.ctx, env.arena).ToUint64());
      rev.push_back({true, std::min(a, b), std::max(a, b)});
    } else {
      rev.push_back({false, a, a});
    }
    e = e->base;
  }
  if (e == nullptr) return false;
  if (e->kind == ExprKind::kIdentifier) {
    base_name = std::string(e->text);
  } else if (e->kind == ExprKind::kMemberAccess && !e->is_scope_resolution) {
    base_name = FlattenHierPath(e);
  } else {
    return false;
  }
  subs.assign(rev.rbegin(), rev.rend());
  return true;
}

static void DimBounds(const ArrayInfo* ai, size_t d, int64_t& lo,
                      int64_t& size) {
  if (ai->dim_sizes.empty()) {
    lo = ai->lo;
    size = ai->size;
  } else {
    lo = ai->dim_los[d];
    size = ai->dim_sizes[d];
  }
}

struct MemLoadArgs {
  MemSlice slice;
  ReadmemWindow w;
};

struct DestArray {
  const std::string& mem_name;
  const ArrayInfo* ai;
};

static void LoadMemQueue(const ReadmemEnv& env, const std::string& content,
                         QueueObject* q, const EnumTypeInfo* enum_info,
                         const MemLoadArgs& args) {
  const MemSlice& slice = args.slice;
  int64_t low_addr = 0;
  int64_t high_addr = static_cast<int64_t>(q->elements.size()) - 1;
  if (slice.is_slice) {
    low_addr = std::max(slice.slice_lo, low_addr);
    high_addr = std::min(slice.slice_hi, high_addr);
  }
  IndexedLoadReq req{{low_addr, high_addr, slice.is_slice},
                     {q->elem_width, !q->is_4state, enum_info},
                     args.w};
  EvalReadmemIndexed(env, content, req, [&](int64_t addr, const Logic4Vec& v) {
    q->elements[static_cast<size_t>(addr)] = v;
  });
}

static void LoadMemSingleDim(const ReadmemEnv& env, const std::string& content,
                             const DestArray& dest,
                             const EnumTypeInfo* enum_info,
                             const MemLoadArgs& args) {
  const ArrayInfo* ai = dest.ai;
  const MemSlice& slice = args.slice;
  int64_t arr_lo = ai->lo;
  int64_t arr_hi = ai->lo + static_cast<int64_t>(ai->size) - 1;
  int64_t low_addr = slice.is_slice ? std::max(slice.slice_lo, arr_lo) : arr_lo;
  int64_t high_addr =
      slice.is_slice ? std::min(slice.slice_hi, arr_hi) : arr_hi;

  IndexedLoadReq req{{low_addr, high_addr, slice.is_slice},
                     {ai->elem_width, !ai->is_4state, enum_info},
                     args.w};
  EvalReadmemIndexed(env, content, req, [&](int64_t addr, const Logic4Vec& v) {
    std::string elem = dest.mem_name + "[" + std::to_string(addr) + "]";
    if (auto* var = env.ctx.FindVariable(elem)) {
      var->value = v;
      var->NotifyWatchers();
    }
  });
}

static const ArrayInfo* LoadMemContainerOrArray(const ReadmemEnv& env,
                                                const std::string& content,
                                                const std::string& mem_name,
                                                const EnumTypeInfo* enum_info,
                                                const MemLoadArgs& args) {
  if (AssocArrayObject* aa = env.ctx.FindAssocArray(mem_name)) {
    EvalReadmemAssoc(env, content, aa,
                     {aa->elem_width, !aa->is_4state, enum_info}, args.w);
    return nullptr;
  }
  if (QueueObject* q = env.ctx.FindQueue(mem_name)) {
    LoadMemQueue(env, content, q, enum_info, args);
    return nullptr;
  }
  return env.ctx.FindArrayInfo(mem_name);
}

static void LoadBareMemName(const ReadmemEnv& env, const std::string& content,
                            const std::string& mem_name,
                            const EnumTypeInfo* enum_info,
                            const ReadmemWindow& w) {
  MemLoadArgs args{MemSlice{false, 0, 0}, w};
  const ArrayInfo* ai =
      LoadMemContainerOrArray(env, content, mem_name, enum_info, args);
  if (!ai) return;
  if (ai->dim_sizes.size() >= 2) {
    EvalReadmemMultiDim(env, content, mem_name, ai,
                        {ai->elem_width, !ai->is_4state, enum_info});
    return;
  }
  LoadMemSingleDim(env, content, {mem_name, ai}, enum_info, args);
}

struct MemLoadRequest {
  const std::string& content;
  const std::string& mem_name;
  const EnumTypeInfo* enum_info;
  const ReadmemWindow& window;
};

static void ReportMemLoadError(const ReadmemEnv& env, const std::string& msg) {
  env.ctx.GetDiag().Error(
      env.loc, "$readmem" + std::string(env.is_hex ? "h" : "b") + ": " + msg,
      Subclause("21.4"));
}

static void LoadSlicedMemName(const ReadmemEnv& env, const MemLoadRequest& req,
                              const MemSubscript& s) {
  MemLoadArgs args{MemSlice{true, s.a, s.b}, req.window};
  const ArrayInfo* ai = LoadMemContainerOrArray(env, req.content, req.mem_name,
                                                req.enum_info, args);
  if (!ai) return;
  LoadMemSingleDim(env, req.content, {req.mem_name, ai}, req.enum_info, args);
}

static bool CheckMemSubscriptShape(const ReadmemEnv& env, const ArrayInfo* ai,
                                   const std::vector<MemSubscript>& subs) {
  size_t total_dims = ai->dim_sizes.empty() ? 1 : ai->dim_sizes.size();
  if (subs.size() > total_dims) {
    ReportMemLoadError(env, "more subscripts than the array has dimensions");
    return false;
  }
  for (size_t i = 0; i + 1 < subs.size(); ++i) {
    if (subs[i].is_slice) {
      ReportMemLoadError(env,
                         "a higher-order dimension must be indexed, not "
                         "sliced");
      return false;
    }
  }
  return true;
}

static bool BuildIndexedMemPrefix(const ReadmemEnv& env, const ArrayInfo* ai,
                                  const std::vector<MemSubscript>& subs,
                                  size_t index_count, std::string& prefix) {
  for (size_t d = 0; d < index_count; ++d) {
    int64_t lo = 0;
    int64_t size = 0;
    DimBounds(ai, d, lo, size);
    if (subs[d].a < lo || subs[d].a >= lo + size) {
      ReportMemLoadError(env, "index outside the bounds of its dimension");
      return false;
    }
    prefix += "[" + std::to_string(subs[d].a) + "]";
  }
  return true;
}

static ArrayInfo SubArrayAtDim(const ArrayInfo* ai, size_t dim) {
  int64_t lo = 0;
  int64_t size = 0;
  DimBounds(ai, dim, lo, size);
  ArrayInfo sub;
  sub.lo = static_cast<uint32_t>(lo);
  sub.size = static_cast<uint32_t>(size);
  sub.elem_width = ai->elem_width;
  sub.is_4state = ai->is_4state;
  return sub;
}

static void LoadRemainingMemDims(const ReadmemEnv& env,
                                 const MemLoadRequest& req, const ArrayInfo* ai,
                                 const std::string& prefix,
                                 size_t index_count) {
  ArrayInfo sub;
  sub.elem_width = ai->elem_width;
  sub.is_4state = ai->is_4state;
  auto skipped = static_cast<std::ptrdiff_t>(index_count);
  sub.dim_los.assign(ai->dim_los.begin() + skipped, ai->dim_los.end());
  sub.dim_sizes.assign(ai->dim_sizes.begin() + skipped, ai->dim_sizes.end());
  sub.lo = sub.dim_los[0];
  sub.size = sub.dim_sizes[0];
  EvalReadmemMultiDim(env, req.content, prefix, &sub,
                      {ai->elem_width, !ai->is_4state, req.enum_info});
}

static void LoadPartiallyIndexedMemName(const ReadmemEnv& env,
                                        const MemLoadRequest& req,
                                        const std::vector<MemSubscript>& subs) {
  const ArrayInfo* ai = env.ctx.FindArrayInfo(req.mem_name);
  if (ai == nullptr) return;
  if (!CheckMemSubscriptShape(env, ai, subs)) return;

  size_t total_dims = ai->dim_sizes.empty() ? 1 : ai->dim_sizes.size();
  bool last_slice = subs.back().is_slice;
  size_t index_count = last_slice ? subs.size() - 1 : subs.size();

  std::string prefix = req.mem_name;
  if (!BuildIndexedMemPrefix(env, ai, subs, index_count, prefix)) return;
  size_t remaining = total_dims - index_count;

  if (last_slice) {
    if (remaining != 1) {
      ReportMemLoadError(env,
                         "a slice is allowed only on the lowest dimension");
      return;
    }
    ArrayInfo sub = SubArrayAtDim(ai, index_count);
    MemLoadArgs args{MemSlice{true, subs.back().a, subs.back().b}, req.window};
    LoadMemSingleDim(env, req.content, {prefix, &sub}, req.enum_info, args);
    return;
  }

  if (remaining == 0) {
    ReportMemLoadError(env,
                       "memory_name resolves to a single element, not an "
                       "array");
    return;
  }

  if (remaining == 1) {
    ArrayInfo sub = SubArrayAtDim(ai, index_count);
    MemLoadArgs args{MemSlice{false, 0, 0}, req.window};
    LoadMemSingleDim(env, req.content, {prefix, &sub}, req.enum_info, args);
    return;
  }

  LoadRemainingMemDims(env, req, ai, prefix, index_count);
}

static bool TryLoadClassArrayProperty(const ReadmemEnv& env,
                                      const std::string& content,
                                      const Expr* mn, const ReadmemWindow& w) {
  const Expr* base = mn;
  MemSlice slice{false, 0, 0};
  if (mn->kind == ExprKind::kSelect && mn->index_end != nullptr &&
      !mn->is_part_select_plus && !mn->is_part_select_minus) {
    base = mn->base;
    auto a = static_cast<int64_t>(
        EvalExpr(mn->index, env.ctx, env.arena).ToUint64());
    auto b = static_cast<int64_t>(
        EvalExpr(mn->index_end, env.ctx, env.arena).ToUint64());
    slice = {true, std::min(a, b), std::max(a, b)};
  }
  ClassArrayRef ref;
  if (!ResolveClassArray(base, env.ctx, env.arena, ref)) return false;
  int64_t arr_hi = ref.lo + static_cast<int64_t>(ref.size) - 1;
  int64_t low_addr = slice.is_slice ? std::max(slice.slice_lo, ref.lo) : ref.lo;
  int64_t high_addr =
      slice.is_slice ? std::min(slice.slice_hi, arr_hi) : arr_hi;
  IndexedLoadReq req{{low_addr, high_addr, slice.is_slice},
                     {ref.prop->width, !ref.prop->is_4state, nullptr},
                     w};
  EvalReadmemIndexed(env, content, req, [&](int64_t addr, const Logic4Vec& v) {
    StoreClassArrayElement(ref, addr, v, env.ctx, env.arena);
  });
  return true;
}

void DoMemLoad(const ReadmemEnv& env, const std::string& content,
               const Expr* mn, const ReadmemWindow& w) {
  if (TryLoadClassArrayProperty(env, content, mn, w)) return;
  std::string mem_name;
  std::vector<MemSubscript> subs;
  if (!CollectMemSubscripts(env, mn, mem_name, subs)) {
    return;
  }

  const EnumTypeInfo* enum_info = env.ctx.GetVariableEnumType(mem_name);

  if (subs.empty()) {
    LoadBareMemName(env, content, mem_name, enum_info, w);
    return;
  }
  if (subs.size() == 1 && subs[0].is_slice) {
    LoadSlicedMemName(env, {content, mem_name, enum_info, w}, subs[0]);
    return;
  }
  LoadPartiallyIndexedMemName(env, {content, mem_name, enum_info, w}, subs);
}

Logic4Vec EvalReadmem(const Expr* expr, SimContext& ctx, Arena& arena,
                      bool is_hex) {
  if (expr->args.size() < 2) return MakeLogic4VecVal(arena, 1, 0);
  std::string filename = EvalStringArg(expr->args[0], ctx, arena);

  std::ifstream ifs(filename);
  if (!ifs.is_open()) {
    ctx.GetDiag().Warning(expr->args[0]->range.start,
                          "$readmem" + std::string(is_hex ? "h" : "b") +
                              ": cannot open file: " + filename,
                          Subclause::None());
    return MakeLogic4VecVal(arena, 1, 0);
  }
  std::string content((std::istreambuf_iterator<char>(ifs)),
                      std::istreambuf_iterator<char>());

  bool has_start = expr->args.size() >= 3;
  bool has_finish = expr->args.size() >= 4;
  int64_t start_arg =
      has_start
          ? static_cast<int64_t>(EvalExpr(expr->args[2], ctx, arena).ToUint64())
          : 0;
  int64_t finish_arg =
      has_finish
          ? static_cast<int64_t>(EvalExpr(expr->args[3], ctx, arena).ToUint64())
          : 0;

  ReadmemEnv env{ctx, arena, is_hex, expr->range.start};
  DoMemLoad(env, content, expr->args[1],
            {has_start, has_finish, start_arg, finish_arg});
  return MakeLogic4VecVal(arena, 1, 0);
}

}  // namespace delta
