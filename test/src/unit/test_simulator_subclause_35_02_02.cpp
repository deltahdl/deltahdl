#include <gtest/gtest.h>

#include <vector>

#include "simulator/dpi_runtime.h"

using namespace delta;

// §35.2.2 "Data types": "SystemVerilog data types are the sole data types that
// can cross the boundary between SystemVerilog and a foreign language in either
// direction (i.e., when an imported function is called from SystemVerilog code
// or an exported SystemVerilog function is called from a foreign code)."
//
// The claim these tests rest on is "in either direction". A value arriving on
// the far side of the boundary is the SystemVerilog type the declaration names
// for it — a formal's type for an argument, the declared result type for a
// result — whichever side made the call. Every test below presents a value
// whose type differs from the declared one and whose value the conversion
// visibly changes, so it fails if the value crossed as the caller built it.
//
// Which SystemVerilog types a formal or a result is allowed to have is §35.5.5
// and §35.5.6, tested with those subclauses.
namespace {

// An export whose SystemVerilog body reports the actual it was entered with,
// so a test can read what crossed the boundary into it. `formals` are the
// types the export declares for its arguments, `result_type` the type it
// declares for its result, and `observed` receives the first actual as the
// body saw it. The body hands that same value back as its result.
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

// §35.2.2: the first of the two directions, "when an imported function is
// called from SystemVerilog code". The actual a SystemVerilog caller supplies
// reaches the foreign code as the SystemVerilog type the import's formal
// declares. §35.6.1 owns the copy-in rule that performs the conversion and
// DpiArgumentPassing in test_simulator_subclause_35_06_01.cpp asserts it as
// such; this case is here because §35.2.2 states the two directions as one
// claim, and the export cases below say nothing about symmetry on their own.
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

  // 300 does not fit a byte. The foreign code is entered with 44, the byte the
  // actual becomes; it would see 300 if the value crossed as an int.
  EXPECT_EQ(result.AsInt(), 44);
}

// §35.2.2: the second direction, "when ... an exported SystemVerilog function
// is called from a foreign code". The actual the foreign caller supplies
// reaches the SystemVerilog body as the type the export's formal declares.
TEST(DpiBoundaryDataTypes, ExportActualReachesSvBodyAsItsFormalsType) {
  DpiRuntime rt;
  DpiArgValue observed;
  rt.RegisterExport(
      ReportingExport({DpiArg{"x", DataTypeKind::kShortint, Direction::kInput}},
                      DataTypeKind::kVoid, &observed));

  rt.CallExport("sv_report", {DpiArgValue::FromInt(70000)});

  // 70000 does not fit a shortint. The body is entered with 4464, the shortint
  // the actual becomes; it would see 70000 if the value crossed as an int.
  EXPECT_EQ(observed.AsInt(), 4464);
}

// §35.2.2: the same direction reached through DpiRuntime::CallExportFromImport,
// which is the entry point foreign code running inside a DPI import call takes
// to an exported SystemVerilog function. The formal's declared type is what
// arrives here too, so which of the two entry points the foreign caller uses
// does not decide what crosses.
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

  // 1000 does not fit a byte. The body is entered with -24, the byte the actual
  // becomes; it would see 1000 if the value crossed as an int.
  EXPECT_EQ(observed.AsInt(), -24);
}

// §35.2.2: a result crosses the boundary as well, and it crosses as a
// SystemVerilog data type — the one the export's declaration gives its result.
// The formal here is the type the actual already has, so the value the foreign
// caller reads back reports the result conversion alone.
TEST(DpiBoundaryDataTypes, ExportResultLeavesAsItsDeclaredType) {
  DpiRuntime rt;
  DpiArgValue observed;
  rt.RegisterExport(
      ReportingExport({DpiArg{"x", DataTypeKind::kInt, Direction::kInput}},
                      DataTypeKind::kByte, &observed));

  DpiArgValue result = rt.CallExport("sv_report", {DpiArgValue::FromInt(258)});

  // The body hands back the int 258 and the export declares a byte result, so
  // 2 leaves across the boundary; 258 would leave if the result crossed as the
  // int the body computed.
  EXPECT_EQ(result.AsInt(), 2);
}

// §35.2.2 names the type each argument crosses as, and DpiRtExport records
// those types per position. A position the declaration describes no type for
// has no declared type to convert to, so the value stands as the caller built
// it. That default is what leaves an export registered without argument types
// passing the values it passed before DpiRtExport could carry any.
TEST(DpiBoundaryDataTypes, ExportWithNoDeclaredFormalTypesLeavesActualsAlone) {
  DpiRuntime rt;
  DpiArgValue observed;
  rt.RegisterExport(ReportingExport({}, DataTypeKind::kVoid, &observed));

  rt.CallExport("sv_report", {DpiArgValue::FromReal(3.75)});

  // 3.75 reaches the body as itself. A position converted to the int a DpiArg
  // declares by default would have rounded it to 4.
  EXPECT_DOUBLE_EQ(observed.AsReal(), 3.75);
}

}  // namespace
