#include <gtest/gtest.h>

#include <vector>

#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_runtime.h"

using namespace delta;

namespace {

DpiRtExport ReportingExport(const std::vector<DpiArg>& formals,
                            DataTypeKind result_type, DpiArgValue* observed) {
  DpiRtExport exp;
  exp.c_name = "c_report";
  exp.sv_name = "sv_report";
  exp.args = formals;
  exp.return_type = result_type;
  exp.impl = [observed](const std::vector<DpiArgValue>& args) {
    *observed = args[0];
    return args[0];
  };
  return exp;
}

TEST(DpiBoundaryDataTypes, ImportActualReachesForeignCodeAsItsFormalsType) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_report";
  func.sv_name = "sv_report";
  func.return_type = DataTypeKind::kInt;
  func.args = {DpiArg{"x", DataTypeKind::kByte, Direction::kInput}};
  func.impl = [](const std::vector<DpiArgValue>& args) {
    return DpiArgValue::FromInt(args[0].AsInt());
  };
  rt.RegisterImport(func);

  std::vector<DpiArgValue> actuals = {DpiArgValue::FromInt(300)};
  DpiArgValue result = rt.CallImportWithArgs("sv_report", actuals);

  EXPECT_EQ(result.AsInt(), 44);
}

TEST(DpiBoundaryDataTypes, ExportActualReachesSvBodyAsItsFormalsType) {
  DpiRuntime rt;
  DpiArgValue observed;
  rt.RegisterExport(
      ReportingExport({DpiArg{"x", DataTypeKind::kShortint, Direction::kInput}},
                      DataTypeKind::kVoid, &observed));

  rt.CallExport("sv_report", {DpiArgValue::FromInt(70000)});

  EXPECT_EQ(observed.AsInt(), 4464);
}

TEST(DpiBoundaryDataTypes, ExportCalledFromAnImportGetsItsFormalsType) {
  DpiRuntime rt;
  DpiArgValue observed;
  rt.RegisterExport(
      ReportingExport({DpiArg{"x", DataTypeKind::kByte, Direction::kInput}},
                      DataTypeKind::kVoid, &observed));

  DpiScope scope;
  scope.name = "top";
  rt.EnterContextImportCall("ctx_import", scope);

  DpiArgValue result;
  rt.CallExportFromImport("sv_report", {DpiArgValue::FromInt(1000)}, &result);

  EXPECT_EQ(observed.AsInt(), -24);
}

TEST(DpiBoundaryDataTypes, ExportResultLeavesAsItsDeclaredType) {
  DpiRuntime rt;
  DpiArgValue observed;
  rt.RegisterExport(
      ReportingExport({DpiArg{"x", DataTypeKind::kInt, Direction::kInput}},
                      DataTypeKind::kByte, &observed));

  DpiArgValue result = rt.CallExport("sv_report", {DpiArgValue::FromInt(258)});

  EXPECT_EQ(result.AsInt(), 2);
}

TEST(DpiBoundaryDataTypes, ExportWithNoDeclaredFormalTypesLeavesActualsAlone) {
  DpiRuntime rt;
  DpiArgValue observed;
  rt.RegisterExport(ReportingExport({}, DataTypeKind::kVoid, &observed));

  rt.CallExport("sv_report", {DpiArgValue::FromReal(3.75)});

  EXPECT_DOUBLE_EQ(observed.AsReal(), 3.75);
}

}  // namespace
