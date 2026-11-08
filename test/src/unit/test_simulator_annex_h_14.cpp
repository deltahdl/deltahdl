#include <gtest/gtest.h>

#include <cstdint>
#include <utility>

#include "simulator/dpi_runtime.h"

using namespace delta;

namespace {

DpiRtFunction Sv31aImport(const char* sv_name) {
  DpiRtFunction func;
  func.c_name = "c_packed";
  func.sv_name = sv_name;
  func.packed_arg_passing = DpiPackedArgPassing::kSv31aReference;
  return func;
}

TEST(Sv31aPackedDataAccess, Sv31aImportIsHandedTheAddressOfTheActual) {
  DpiRuntime rt;
  rt.RegisterImport(Sv31aImport("packed_31a"));
  uint32_t actual[4] = {1, 2, 3, 4};

  EXPECT_EQ(rt.PackedArgRef("packed_31a", actual), actual);
}

TEST(Sv31aPackedDataAccess, AWriteThroughTheSv31aReferenceReachesTheActual) {
  DpiRuntime rt;
  rt.RegisterImport(Sv31aImport("packed_31a"));
  uint32_t actual[4] = {1, 2, 3, 4};

  auto* ref = static_cast<uint32_t*>(rt.PackedArgRef("packed_31a", actual));
  ref[2] = 0xfeedbeefu;

  EXPECT_EQ(actual[2], 0xfeedbeefu);
}

TEST(Sv31aPackedDataAccess, AnIeee1800ImportIsHandedNoReferenceToTheActual) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_packed";
  func.sv_name = "packed_1800";
  rt.RegisterImport(std::move(func));
  uint32_t actual[4] = {1, 2, 3, 4};

  EXPECT_EQ(rt.PackedArgRef("packed_1800", actual), nullptr);
}

TEST(Sv31aPackedDataAccess, AnUndeclaredImportIsHandedNoReferenceToTheActual) {
  DpiRuntime rt;
  uint32_t actual[4] = {1, 2, 3, 4};

  EXPECT_EQ(rt.PackedArgRef("never_declared", actual), nullptr);
}

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
