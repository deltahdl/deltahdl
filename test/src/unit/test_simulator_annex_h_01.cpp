#include <gtest/gtest.h>

#include <string_view>
#include <vector>

#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_runtime.h"
#include "simulator/dpi_side.h"

using namespace delta;

// Annex H.1 says what the annex is about: the foreign language side of the
// DPI. The interface has two sides, and a subroutine crossing it is
// implemented on one and called from the other under that side's name for
// it. The cases check which clause describes each side, which side
// implements and which calls an import and an export, and that the runtime
// knows a subroutine on the SystemVerilog side by its SystemVerilog name and
// on the foreign side by its linkage name, each name reaching it on its own
// side and not on the other.

namespace {

// §H.1: the annex describes the foreign language side; Clause 35 the
// SystemVerilog side.
TEST(DpiForeignSide, TheAnnexDescribesTheForeignSide) {
  EXPECT_EQ(DpiSideDescribedIn(DpiSide::kForeign), "H");
  EXPECT_EQ(DpiSideDescribedIn(DpiSide::kSystemVerilog), "35");
}

// §H.1 with §H.2: an import is implemented on the foreign side and called
// from the SystemVerilog side; an export the other way about.
TEST(DpiForeignSide, EachKindIsImplementedOnOneSideAndCalledFromTheOther) {
  DpiRtFunction import;
  DpiRtExport exported;
  EXPECT_EQ(DpiImplementingSide(import), DpiSide::kForeign);
  EXPECT_EQ(DpiCallingSide(import), DpiSide::kSystemVerilog);
  EXPECT_EQ(DpiImplementingSide(exported), DpiSide::kSystemVerilog);
  EXPECT_EQ(DpiCallingSide(exported), DpiSide::kForeign);
  EXPECT_NE(DpiImplementingSide(import), DpiCallingSide(import));
  EXPECT_NE(DpiImplementingSide(exported), DpiCallingSide(exported));
}

// §H.1 with §35.4: a subroutine is known on each side by that side's name.
// The runtime finds an import under its SystemVerilog name where the
// SystemVerilog side calls it and under its linkage name where the foreign
// side links it, and neither name reaches it on the other side; likewise an
// export.
TEST(DpiForeignSide, EachSideKnowsASubroutineByItsOwnName) {
  DpiRuntime rt;
  DpiRtFunction import;
  import.c_name = "c_side_name";
  import.sv_name = "sv_side_name";
  import.return_type = DataTypeKind::kInt;
  import.impl = [](const std::vector<DpiArgValue>&) {
    return DpiArgValue::FromInt(1);
  };
  rt.RegisterImport(import);
  EXPECT_EQ(DpiNameOnSide(import, DpiSide::kSystemVerilog), "sv_side_name");
  EXPECT_EQ(DpiNameOnSide(import, DpiSide::kForeign), "c_side_name");
  EXPECT_NE(rt.FindImport(DpiNameOnSide(import, DpiSide::kSystemVerilog)),
            nullptr);
  EXPECT_EQ(rt.FindImport(DpiNameOnSide(import, DpiSide::kForeign)), nullptr);
  EXPECT_NE(rt.FindImportByGlobalName(DpiNameOnSide(import, DpiSide::kForeign)),
            nullptr);
  EXPECT_EQ(
      rt.FindImportByGlobalName(DpiNameOnSide(import, DpiSide::kSystemVerilog)),
      nullptr);

  DpiRtExport exported;
  exported.c_name = "c_exported";
  exported.sv_name = "sv_exported";
  exported.impl = [](const std::vector<DpiArgValue>&) {
    return DpiArgValue::FromInt(2);
  };
  rt.RegisterExport(exported);
  EXPECT_EQ(DpiNameOnSide(exported, DpiSide::kSystemVerilog), "sv_exported");
  EXPECT_EQ(DpiNameOnSide(exported, DpiSide::kForeign), "c_exported");
  EXPECT_NE(rt.FindExport(DpiNameOnSide(exported, DpiSide::kSystemVerilog)),
            nullptr);
  EXPECT_EQ(rt.FindExport(DpiNameOnSide(exported, DpiSide::kForeign)), nullptr);
  EXPECT_NE(
      rt.FindExportByGlobalName(DpiNameOnSide(exported, DpiSide::kForeign)),
      nullptr);
  EXPECT_EQ(rt.FindExportByGlobalName(
                DpiNameOnSide(exported, DpiSide::kSystemVerilog)),
            nullptr);

  // A declaration giving no linkage name is known on the foreign side by its
  // SystemVerilog name, so the one name reaches it on both sides.
  DpiRtFunction unnamed;
  unnamed.sv_name = "same_on_both";
  unnamed.return_type = DataTypeKind::kInt;
  unnamed.impl = [](const std::vector<DpiArgValue>&) {
    return DpiArgValue::FromInt(3);
  };
  rt.RegisterImport(unnamed);
  EXPECT_EQ(DpiNameOnSide(unnamed, DpiSide::kForeign), "same_on_both");
  EXPECT_NE(rt.FindImportByGlobalName("same_on_both"), nullptr);
  EXPECT_NE(rt.FindImport("same_on_both"), nullptr);
}

}  // namespace
