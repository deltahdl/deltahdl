#include <gtest/gtest.h>

#include <string_view>
#include <utility>
#include <vector>

#include "simulator/dpi_runtime.h"

using namespace delta;

// §35.5.1.3 Special properties pure and context.
//
// The subclause gives an imported subroutine one special property, the other,
// or neither, and says what each of the three admits:
//
//   Special properties can be specified for an imported subroutine as pure or
//   as context.
//
//   A function whose result depends solely on the values of its input
//   arguments and with no side effects can be specified as pure. An imported
//   task can never be declared pure.
//
//   An imported subroutine that is intended to call exported subroutines or to
//   access SystemVerilog data objects other than its actual arguments shall be
//   specified as context. A subroutine not specified as context shall not read
//   or write any data objects from SystemVerilog other than its actual
//   arguments.
//
//   If neither the pure nor the context attribute is used on an imported
//   subroutine, the subroutine shall not access SystemVerilog data objects;
//   however, it can perform side effects such as writing to a file or
//   manipulating a global variable.
//
// The task sentence is answered where a declaration is read, by ParseDpiImport
// in src/parser/parser_dpi.cpp, and is covered in
// test_parser_subclause_35_05_01_03.cpp. What is left for a run is the third
// state, which no other subclause of §35.5 describes: §35.5.2 says what a pure
// function may do and §35.5.3 what a context one may, and neither says
// anything about a subroutine declared with no property at all. This file
// reads that state off DpiRuntime in src/simulator/dpi_runtime.h.
//
// Two things distinguish it. A subroutine declared with neither property may
// not reach a SystemVerilog data object, which the runtime settles by opening
// its call as a noncontext one: DpiRuntime::EnterDeclaredImportCall takes the
// frame's property from the declaration, so an import declared pure gets a
// noncontext frame as well, which is the case §35.5.3 never mentions. And it
// may have side effects, so its call is made every time it is written rather
// than answered from what an earlier call returned.

namespace {

// One import declared with the properties a case names, and the count its own
// foreign body keeps.
//
// The count is the side effect §35.5.1.3 permits: a variable belonging to the
// foreign code, which the body manipulates on every call and no SystemVerilog
// data object is touched to keep. Reading it back is how a case asks whether
// the call was made. The import's one formal is an inout so that the same
// declaration also answers what it is allowed to do to an actual.
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

  // Calls the import once on `actual` and yields what it left in the actual.
  int CallOn(int actual) {
    std::vector<DpiArgValue> actuals = {DpiArgValue::FromInt(actual)};
    rt.CallImportWithArgs("note", actuals);
    return actuals[0].AsInt();
  }
};

// One export, one import declared with the properties a case names, and the
// outcome of asking a call to `entered` to reach that export.
//
// The call is opened through DpiRuntime::EnterDeclaredImportCall, so what the
// declaration says decides the frame rather than what the case asks for. A
// case naming a name no import was registered under reads the fourth answer,
// where there is no declaration to take a property from.
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

// ---------------------------------------------------------------------------
// The properties are alternatives, and neither is one of the answers.
// ---------------------------------------------------------------------------

// A declaration carrying no property carries neither, which is the state
// §35.5.1.3's last paragraph is about. A registration that supplied one of its
// own would leave that paragraph describing nothing this runtime can hold.
TEST(DpiSpecialProperties, ADeclarationWithNoPropertyCarriesNeither) {
  CountingItsOwnCalls declared(/*is_pure=*/false, /*is_context=*/false);
  const DpiRtFunction* func = declared.rt.FindImport("note");
  ASSERT_NE(func, nullptr);
  EXPECT_FALSE(func->is_pure || func->is_context);
}

// §35.5.1.3 offers pure or context, so a subroutine specified as pure is not
// thereby specified as context. Without this the case above would hold of a
// runtime that kept one flag and reported it under both names.
TEST(DpiSpecialProperties, ADeclarationSpecifiedPureIsNotSpecifiedContext) {
  CountingItsOwnCalls declared(/*is_pure=*/true, /*is_context=*/false);
  const DpiRtFunction* func = declared.rt.FindImport("note");
  ASSERT_NE(func, nullptr);
  EXPECT_FALSE(func->is_context);
}

// ---------------------------------------------------------------------------
// Neither property: no SystemVerilog data object.
// ---------------------------------------------------------------------------

// An exported subroutine is the one SystemVerilog object a foreign body can
// reach from inside a call here, and a subroutine declared with neither
// property shall not reach it. The declaration alone decides that: nothing at
// the call site asked for a noncontext frame.
TEST(DpiSpecialProperties, ACallDeclaringNeitherPropertyCannotReachAnExport) {
  ReachingAnExport reaching(/*is_pure=*/false, /*is_context=*/false, "note");
  EXPECT_EQ(reaching.status, DpiExportCallStatus::kNoncontextChain);
}

// A subroutine specified as pure is equally not specified as context, so it is
// refused for the same reason. §35.5.3 describes only the context and the
// noncontext subroutine and never names this one, so §35.5.1.3 is what settles
// it.
TEST(DpiSpecialProperties, ACallDeclaredPureCannotReachAnExport) {
  ReachingAnExport reaching(/*is_pure=*/true, /*is_context=*/false, "note");
  EXPECT_EQ(reaching.status, DpiExportCallStatus::kNoncontextChain);
}

// A name no declaration was registered under states no property, which is the
// same as stating neither, so it is refused too rather than trusted with the
// scope the call site offered.
TEST(DpiSpecialProperties, ACallOfAnUndeclaredNameCannotReachAnExport) {
  ReachingAnExport reaching(/*is_pure=*/true, /*is_context=*/true, "unknown");
  EXPECT_EQ(reaching.status, DpiExportCallStatus::kNoncontextChain);
}

// The subroutine that is specified as context does reach it, and gets the
// export's result. Without this the three cases above would hold of a runtime
// that refused every export call whatever the declaration said.
TEST(DpiSpecialProperties, ACallDeclaredContextReachesTheExport) {
  ReachingAnExport reaching(/*is_pure=*/false, /*is_context=*/true, "note");
  ASSERT_EQ(reaching.status, DpiExportCallStatus::kOk);
  EXPECT_EQ(reaching.result.AsInt(), 9);
}

// ---------------------------------------------------------------------------
// Neither property: side effects are still permitted.
// ---------------------------------------------------------------------------

// §35.5.1.3 lets a subroutine declared with neither property manipulate a
// global variable, so its result need not be the same twice and the call has
// to be made every time it is written. Two calls on one actual therefore run
// the body twice. Only §35.5.2's pure function may be answered from what an
// earlier call returned.
TEST(DpiSpecialProperties, ACallDeclaringNeitherPropertyIsMadeEveryTime) {
  CountingItsOwnCalls declared(/*is_pure=*/false, /*is_context=*/false);
  declared.CallOn(0);
  declared.CallOn(0);
  EXPECT_EQ(declared.calls, 2);
}

// And the side effect is what the second call is decided by, so the two calls
// leave different values in the same actual. Without this the case above would
// hold of a runtime that ran the body twice and returned the first answer.
TEST(DpiSpecialProperties, TheSecondCallAnswersFromTheSideEffect) {
  CountingItsOwnCalls declared(/*is_pure=*/false, /*is_context=*/false);
  EXPECT_NE(declared.CallOn(0), declared.CallOn(0));
}

// ---------------------------------------------------------------------------
// Neither property: the actual arguments are still its own.
// ---------------------------------------------------------------------------

// §35.5.1.3 bars such a subroutine from data objects other than its actual
// arguments, which leaves the actual arguments to it. So the value the foreign
// body wrote to its inout formal reaches the actual, and the prohibition above
// is about what the subroutine may reach past its arguments rather than about
// the arguments themselves.
TEST(DpiSpecialProperties, ACallDeclaringNeitherPropertyStillWritesItsActual) {
  CountingItsOwnCalls declared(/*is_pure=*/false, /*is_context=*/false);
  EXPECT_EQ(declared.CallOn(10), 11);
}

}  // namespace
