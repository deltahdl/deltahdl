// §6.6.7 and §6.7.3: the resolution and time-zero initialization of a net of a
// user-defined nettype, moved out of src/simulator/net.cpp, which resolves the
// built-in net types, at its size limit.

#include <cstdint>
#include <vector>

#include "common/types.h"
#include "simulator/net.h"
#include "simulator/variable.h"

namespace delta {

static void SetAllX(Logic4Vec& val) {
  for (uint32_t w = 0; w < val.nwords; ++w) {
    val.words[w] = {~uint64_t{0}, ~uint64_t{0}};  // x = (aval=1, bval=1)
  }
}

bool ValidateNettypeDataKind(NettypeDataKind kind) {
  switch (kind) {
    case NettypeDataKind::k4StateIntegral:
    case NettypeDataKind::k2StateIntegral:
    case NettypeDataKind::kReal:
    case NettypeDataKind::kShortreal:
    case NettypeDataKind::kFixedUnpackedArray:
      return true;
    case NettypeDataKind::kDynamicArray:
    case NettypeDataKind::kString:
    case NettypeDataKind::kClass:
      return false;
  }
  return false;
}

bool ResolveUserDefinedNet(Net& net, const UserNettype& nettype, Arena& arena) {
  // With a resolution function the whole driver set is handed to the function,
  // which computes the single atomic value of the net. Without one the net is
  // left at its existing value (an undriven nettype net is unknown).
  if (nettype.resolution) {
    Logic4Vec result = nettype.resolution(arena, net.drivers);
    net.resolved->value = result;
  } else if (net.drivers.empty() && net.resolved) {
    // §6.6.7/§6.7.3: a logic net of an unresolved user-defined nettype with no
    // drivers takes the data type's default value, which for a 4-state type is
    // x (not z and not 0).
    SetAllX(net.resolved->value);
  }
  return true;
}

bool CheckUnresolvedMultipleDrivers(const Net& net, const UserNettype& nt) {
  return !nt.resolution && net.drivers.size() > 1;
}

// The 4-state data types default to x; the 2-state, real, and shortreal types
// default to a zero bit pattern. §6.7.3 leans on these defaults via Table 6-7.
static bool DataTypeDefaultsToX(NettypeDataKind kind) {
  switch (kind) {
    case NettypeDataKind::k4StateIntegral:
    case NettypeDataKind::kFixedUnpackedArray:
      return true;
    case NettypeDataKind::k2StateIntegral:
    case NettypeDataKind::kReal:
    case NettypeDataKind::kShortreal:
    case NettypeDataKind::kDynamicArray:
    case NettypeDataKind::kString:
    case NettypeDataKind::kClass:
      return false;
  }
  return true;
}

static void SetAllZero(Logic4Vec& val) {
  for (uint32_t w = 0; w < val.nwords; ++w) {
    val.words[w] = {0, 0};
  }
}

static void SetBit(Logic4Vec& val, uint32_t bit, uint64_t aval, uint64_t bval) {
  uint32_t w = bit / 64;
  uint64_t mask = uint64_t{1} << (bit % 64);
  if (aval & 1) {
    val.words[w].aval |= mask;
  } else {
    val.words[w].aval &= ~mask;
  }
  if (bval & 1) {
    val.words[w].bval |= mask;
  } else {
    val.words[w].bval &= ~mask;
  }
}

bool InitializeUserDefinedNet(Net& net, const UserNettype& nettype,
                              Arena& arena) {
  if (!net.resolved) return false;

  // §6.7.3: the initial value is the data-type default and must be in place
  // before the guaranteed resolution call (and before any procedure starts).
  if (DataTypeDefaultsToX(nettype.data_kind)) {
    SetAllX(net.resolved->value);
  } else {
    SetAllZero(net.resolved->value);
  }

  // §6.7.3: a resolved nettype's resolution function is activated at least once
  // at time zero -- even for an undriven net, where it sees an empty driver
  // set.
  if (nettype.resolution) {
    net.resolved->value = nettype.resolution(arena, net.drivers);
  }
  return true;
}

Logic4Vec InitialStructNetValue(Arena& arena, uint32_t total_width,
                                const std::vector<StructMemberInit>& members) {
  Logic4Vec value = MakeLogic4Vec(arena, total_width);
  // §6.7.3: members with no initializer keep the 4-state data-type default (x).
  SetAllX(value);
  // §6.7.3: any initialization expression for a struct member is applied.
  for (const auto& m : members) {
    if (!m.has_initializer) continue;
    for (uint32_t b = 0; b < m.width; ++b) {
      uint32_t src = b / 64;
      uint64_t bitmask = uint64_t{1} << (b % 64);
      uint64_t a = (m.init_value.words[src].aval & bitmask) ? 1 : 0;
      uint64_t bv = (m.init_value.words[src].bval & bitmask) ? 1 : 0;
      SetBit(value, m.offset + b, a, bv);
    }
  }
  return value;
}

}  // namespace delta
