#include <gtest/gtest.h>

#include <cstdint>
#include <utility>

#include "simulator/dpi_runtime.h"

using namespace delta;

namespace {

// Annex H.14 describes the SV3.1a semantics for packed array arguments and
// deprecates them: the functionality "need not be implemented by an IEEE Std
// 1800 simulator". A declaration therefore has to ask for them, and this builds
// one that does.
DpiRtFunction Sv31aImport(const char* sv_name) {
  DpiRtFunction func;
  func.c_name = "c_packed";
  func.sv_name = sv_name;
  func.packed_arg_passing = DpiPackedArgPassing::kSv31aReference;
  return func;
}

// §H.14: "in SV3.1a, packed data arguments are passed by opaque handle types
// svLogicPackedArrRef and svBitPackedArrRef." The handle refers to the
// simulator's own representation of the array, so what the foreign code
// receives is the actual itself rather than anything derived from it.
TEST(Sv31aPackedDataAccess, Sv31aImportIsHandedTheAddressOfTheActual) {
  DpiRuntime rt;
  rt.RegisterImport(Sv31aImport("packed_31a"));
  uint32_t actual[4] = {1, 2, 3, 4};

  EXPECT_EQ(rt.PackedArgRef("packed_31a", actual), actual);
}

// §H.14: an implementation passing packed data this way "need not do any
// conversion or marshalling of data into the canonical format". Nothing is
// copied in either direction, so a value the foreign code writes through the
// handle is in the caller's array the moment it is written.
TEST(Sv31aPackedDataAccess, AWriteThroughTheSv31aReferenceReachesTheActual) {
  DpiRuntime rt;
  rt.RegisterImport(Sv31aImport("packed_31a"));
  uint32_t actual[4] = {1, 2, 3, 4};

  auto* ref = static_cast<uint32_t*>(rt.PackedArgRef("packed_31a", actual));
  ref[2] = 0xfeedbeefu;

  EXPECT_EQ(actual[2], 0xfeedbeefu);
}

// §H.14 states the SV3.1a handle as the difference from IEEE Std 1800
// semantics, under which packed data reaches the foreign code as the canonical
// representation §H.10.1.2 defines. An import declared under those semantics is
// handed no reference to its actual, because the canonical form the foreign
// code reads is not the actual.
TEST(Sv31aPackedDataAccess, AnIeee1800ImportIsHandedNoReferenceToTheActual) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_packed";
  func.sv_name = "packed_1800";
  rt.RegisterImport(std::move(func));
  uint32_t actual[4] = {1, 2, 3, 4};

  EXPECT_EQ(rt.PackedArgRef("packed_1800", actual), nullptr);
}

// §H.14 makes the SV3.1a semantics deprecated functionality a simulator need
// not implement, so they are never what a call gets by default. A name no
// declaration was registered under asked for nothing and gets the canonical
// representation.
TEST(Sv31aPackedDataAccess, AnUndeclaredImportIsHandedNoReferenceToTheActual) {
  DpiRuntime rt;
  uint32_t actual[4] = {1, 2, 3, 4};

  EXPECT_EQ(rt.PackedArgRef("never_declared", actual), nullptr);
}

// §H.14's backwards compatibility is offered per declaration and not per
// simulator: one import in a design can take the deprecated semantics while
// another takes the IEEE Std 1800 ones, and the two are passed their packed
// data differently in the same run.
TEST(Sv31aPackedDataAccess, ThePassingSemanticsAreChosenPerDeclaration) {
  DpiRuntime rt;
  rt.RegisterImport(Sv31aImport("packed_31a"));
  DpiRtFunction canonical;
  canonical.c_name = "c_canonical";
  canonical.sv_name = "packed_1800";
  rt.RegisterImport(std::move(canonical));
  uint32_t actual[4] = {1, 2, 3, 4};

  EXPECT_EQ(rt.PackedArgRef("packed_31a", actual), actual);
  EXPECT_EQ(rt.PackedArgRef("packed_1800", actual), nullptr);
}

}  // namespace
