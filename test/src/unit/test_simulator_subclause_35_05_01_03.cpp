#include <gtest/gtest.h>

#include <string_view>
#include <utility>
#include <vector>

#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_runtime.h"

using namespace delta;

namespace {

struct CountingItsOwnCalls {
  DpiRuntime rt;
  int calls = 0;

  CountingItsOwnCalls(bool is_pure, bool is_context) {
    DpiRtFunction func;
    func.c_name = "c_note";
    func.sv_name = "note";
    func.return_type = DataTypeKind::kInt;
    func.args = {DpiArg{"io", DataTypeKind::kInt, Direction::kInout}};
    func.is_pure = is_pure;
    func.is_context = is_context;
    func.arg_impl = [this](std::vector<DpiArgValue>& a) {
      ++calls;
      a[0] = DpiArgValue::FromInt(a[0].AsInt() + calls);
      return DpiArgValue::FromInt(calls);
    };
    rt.RegisterImport(std::move(func));
  }

  int CallOn(int actual) {
    std::vector<DpiArgValue> actuals = {DpiArgValue::FromInt(actual)};
    rt.CallImportWithArgs("note", actuals);
    return actuals[0].AsInt();
  }
};

struct ReachingAnExport {
  DpiRuntime rt;
  DpiArgValue result;
  DpiExportCallStatus status = DpiExportCallStatus::kOk;

  ReachingAnExport(bool is_pure, bool is_context, std::string_view entered) {
    DpiRtExport exp;
    exp.sv_name = "sv_export";
    exp.impl = [](const std::vector<DpiArgValue>&) {
      return DpiArgValue::FromInt(9);
    };
    rt.RegisterExport(exp);

    DpiRtFunction func;
    func.c_name = "c_note";
    func.sv_name = "note";
    func.is_pure = is_pure;
    func.is_context = is_context;
    rt.RegisterImport(std::move(func));

    DpiScope scope;
    scope.name = "top.dut";
    rt.EnterDeclaredImportCall(entered, scope);
    status = rt.CallExportFromImport("sv_export", {}, &result);
  }
};

TEST(DpiSpecialProperties, ADeclarationWithNoPropertyCarriesNeither) {
  CountingItsOwnCalls declared(false, false);
  const DpiRtFunction* func = declared.rt.FindImport("note");
  ASSERT_NE(func, nullptr);
  EXPECT_FALSE(func->is_pure || func->is_context);
}

TEST(DpiSpecialProperties, ADeclarationSpecifiedPureIsNotSpecifiedContext) {
  CountingItsOwnCalls declared(true, false);
  const DpiRtFunction* func = declared.rt.FindImport("note");
  ASSERT_NE(func, nullptr);
  EXPECT_FALSE(func->is_context);
}

TEST(DpiSpecialProperties, ACallDeclaringNeitherPropertyCannotReachAnExport) {
  ReachingAnExport reaching(false, false, "note");
  EXPECT_EQ(reaching.status, DpiExportCallStatus::kNoncontextChain);
}

TEST(DpiSpecialProperties, ACallDeclaredPureCannotReachAnExport) {
  ReachingAnExport reaching(true, false, "note");
  EXPECT_EQ(reaching.status, DpiExportCallStatus::kNoncontextChain);
}

TEST(DpiSpecialProperties, ACallOfAnUndeclaredNameCannotReachAnExport) {
  ReachingAnExport reaching(true, true, "unknown");
  EXPECT_EQ(reaching.status, DpiExportCallStatus::kNoncontextChain);
}

TEST(DpiSpecialProperties, ACallDeclaredContextReachesTheExport) {
  ReachingAnExport reaching(false, true, "note");
  ASSERT_EQ(reaching.status, DpiExportCallStatus::kOk);
  EXPECT_EQ(reaching.result.AsInt(), 9);
}

TEST(DpiSpecialProperties, ACallDeclaringNeitherPropertyIsMadeEveryTime) {
  CountingItsOwnCalls declared(false, false);
  declared.CallOn(0);
  declared.CallOn(0);
  EXPECT_EQ(declared.calls, 2);
}

TEST(DpiSpecialProperties, TheSecondCallAnswersFromTheSideEffect) {
  CountingItsOwnCalls declared(false, false);
  EXPECT_NE(declared.CallOn(0), declared.CallOn(0));
}

TEST(DpiSpecialProperties, ACallDeclaringNeitherPropertyStillWritesItsActual) {
  CountingItsOwnCalls declared(false, false);
  EXPECT_EQ(declared.CallOn(10), 11);
}

}  // namespace
