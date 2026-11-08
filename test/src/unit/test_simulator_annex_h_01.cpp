#include <gtest/gtest.h>

#include <string_view>
#include <vector>

#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_runtime.h"
#include "simulator/dpi_side.h"

using namespace delta;

namespace {

TEST(DpiForeignSide, TheAnnexDescribesTheForeignSide) {
  EXPECT_EQ(DpiSideDescribedIn(DpiSide::kForeign), "H");
  EXPECT_EQ(DpiSideDescribedIn(DpiSide::kSystemVerilog), "35");
}

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
