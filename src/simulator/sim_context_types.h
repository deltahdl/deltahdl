#pragma once

#include <array>
#include <cstdint>
#include <cstdio>
#include <deque>
#include <map>
#include <memory>
#include <random>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast.h"
#include "simulator/class_object.h"
#include "simulator/coverage_control.h"
#include "simulator/net.h"
#include "simulator/scheduler.h"
#include "simulator/sync_objects.h"
#include "simulator/variable.h"

namespace delta {

struct ModuleItem;
struct Process;

struct EnumMemberInfo {
  std::string_view name;
  uint64_t value = 0;
};

struct EnumTypeInfo {
  std::string_view type_name;
  std::vector<EnumMemberInfo> members;
};

struct StructTypeInfo;

struct StructFieldInfo {
  std::string_view name;
  uint32_t bit_offset = 0;
  uint32_t width = 0;
  DataTypeKind type_kind = DataTypeKind::kLogic;
  // §7.2.1: the layout of this field's own type when it is itself a struct or
  // union, so a nested member is reachable by its dotted path. Null for
  // scalars.
  const StructTypeInfo* nested = nullptr;
};

struct StructTypeInfo {
  std::string_view type_name;
  std::vector<StructFieldInfo> fields;
  uint32_t total_width = 0;
  bool is_packed = false;
  bool is_union = false;
  bool is_soft = false;
};

// §7.2.1 / §23.6: resolve a (possibly dotted) member path within `info` to the
// absolute bit offset and width within the base variable, descending through
// nested struct/union fields. Returns false if any path segment is not a field.
// When `out_kind` is non-null it receives the resolved member's declared type
// kind, which the read path uses to apply §7.3.1's 4-state-to-2-state
// conversion when a 2-state member of a packed union is read.
bool ResolveStructFieldPath(const StructTypeInfo* info, std::string_view path,
                            uint32_t* bit_offset, uint32_t* width,
                            DataTypeKind* out_kind = nullptr);

struct QueueObject {
  std::vector<Logic4Vec> elements;
  std::vector<uint64_t> element_ids;
  uint32_t elem_width = 32;
  // Whether the element type is 4-state. Fixes the value yielded when an
  // element of the queue is absent (Table 7-1, see 7.4.5): x for 4-state
  // element types, 0 for 2-state ones.
  bool is_4state = true;
  int32_t max_size = -1;
  uint32_t generation = 0;

  uint64_t AllocateId() { return ++next_elem_id_; }

  // §7.10.3: gives every element the queue holds a fresh identity, which is
  // what "when the target of an assignment is an entire queue, references to
  // any element of the original queue shall become outdated" requires.
  void AssignFreshIds();

  // §7.10.3: gives an identity to each element appended since the last call and
  // leaves the identities of the elements already there alone. Growing a queue
  // removes nothing, so every reference taken on it stays valid; only the new
  // elements need identities of their own.
  void AllocateIdsForAppended();

 private:
  uint64_t next_elem_id_ = 0;
};

struct QueueRefBinding {
  QueueObject* queue = nullptr;
  uint64_t element_id = 0;
  Variable* local_var = nullptr;
};

struct AssocArrayObject;

struct AssocRefBinding {
  AssocArrayObject* assoc = nullptr;
  bool is_string_key = false;
  int64_t int_key = 0;
  std::string str_key;
  Variable* local_var = nullptr;
};

struct AssocArrayObject {
  std::map<int64_t, Logic4Vec> int_data;
  std::map<std::string, Logic4Vec> str_data;
  uint32_t elem_width = 32;
  uint32_t index_width = 32;
  bool is_string_key = false;
  bool is_wildcard = false;
  bool is_4state = false;
  // Signedness of an integral index type: controls whether an index expression
  // is sign- or zero-extended to the index width before becoming a key, which
  // in turn fixes the iteration ordering (§7.8.4).
  bool is_index_signed = true;
  bool has_default = false;
  Logic4Vec default_value;
  // §7.8.7: the value an element allocated by a write starts at when the
  // declaration carried no '{default:...}, recorded only when the element type
  // supplies one of its own. A struct whose members carry initializers is the
  // case the subclause gives: `typedef struct {int x=1,y=2;} xy_t;
  // xy_t b[int];` allocates b[2] holding 1 and 2. Table 7-1 (see §7.4.5)
  // governs what a read of a nonexistent entry yields and is a separate
  // question; it names no struct type, so a read still yields x or 0.
  bool has_elem_init = false;
  Logic4Vec elem_init;
  uint32_t Size() const;
};

struct ArrayInfo {
  uint32_t lo = 0;
  uint32_t size = 0;
  uint32_t elem_width = 32;
  bool is_descending = false;
  bool is_dynamic = false;
  bool is_queue = false;
  bool is_4state = true;
  DataTypeKind elem_type_kind = DataTypeKind::kImplicit;
  // §21.4.3: address extents of each unpacked dimension, outermost (leftmost in
  // the declaration) first, for a multidimensional unpacked array. Empty when
  // the array has a single unpacked dimension, in which case lo/size above
  // describe it. $readmemb/$readmemh consult these to fill the array in
  // row-major order and to resolve an @-address against the highest dimension.
  std::vector<uint32_t> dim_los = {};
  std::vector<uint32_t> dim_sizes = {};
};

// §20.15.3: a queued entry as the queue manager retains it. $q_add records the
// job_id and the user-defined inform_id; $q_remove hands both back through its
// output arguments when the entry is taken off the queue. §20.15.5 additionally
// stamps each entry with the simulation time it was placed, so the queue's
// wait-time statistics can be derived when an entry leaves or is examined.
struct StochasticQueueEntry {
  uint64_t job_id = 0;
  uint64_t inform_id = 0;
  uint64_t arrival_tick = 0;
};

// §20.15: per-queue bookkeeping for the stochastic-analysis queue tasks.
// The queue type and capacity validated at creation and the running occupancy
// drive the §20.15.6 status codes (the full and empty conditions of Table
// 20-11). `entries` holds the stored entries in arrival order so that
// §20.15.3 $q_remove can return the job_id/inform_id of the entry it removes,
// selected per the FIFO/LIFO discipline fixed by the q_type (see §20.15.1).
//
// The remaining fields accumulate the activity statistics that §20.15.5
// $q_exam reports through Table 20-10: the peak occupancy ever reached, the
// span and number of arrivals (for the mean interarrival time), and the
// completed-wait totals (count, sum and minimum) gathered as entries are
// removed.
struct StochasticQueue {
  int64_t q_type = 0;
  int64_t max_length = 0;
  uint64_t count = 0;
  std::deque<StochasticQueueEntry> entries = {};

  uint64_t max_count = 0;
  uint64_t arrivals = 0;
  uint64_t first_arrival_tick = 0;
  uint64_t last_arrival_tick = 0;
  uint64_t departures = 0;
  uint64_t total_wait = 0;
  uint64_t shortest_wait = 0;
};

enum class DelayMode : uint8_t { kMin, kTyp, kMax };

// State block governed by $timeformat (see 20.4.3). The four members map
// 1:1 to the task's arguments and persist between invocations.
struct TimeFormatSpec {
  int units_number = -9;
  int precision_number = 0;
  std::string suffix_string;
  int minimum_field_width = 20;
};

// §6.7.1: the optional defining attributes of a net beyond its name, nettype
// and width — charge strength and decay (for trireg), the user-nettype flag,
// the resolution-function name, and whether the net is signed.
struct NetSpec {
  Strength charge_strength = Strength::kMedium;
  uint64_t decay_ticks = 0;
  bool is_user_nettype = false;
  std::string_view resolve_func = {};
  bool is_signed = false;
};

// §7.8: the optional defining attributes of an associative array beyond its
// name, element width and string-key flag — the index width, the wildcard
// (index type [*]) flag, the 4-state-element flag, and whether the integral
// index type is signed.
struct AssocArraySpec {
  uint32_t index_width = 32;
  bool is_wildcard = false;
  bool is_4state = false;
  bool is_index_signed = true;
};

}  // namespace delta
