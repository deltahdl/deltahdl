#include <gtest/gtest.h>

#include <cstdint>
#include <stdexcept>
#include <vector>

#include "simulator/dpi_runtime.h"

using namespace delta;

// §35.5.1.6 "C++ exceptions". "It is possible to implement DPI imported tasks
// and functions using C++, as long as C linkage conventions are observed at the
// language boundary. If C++ is used, exceptions shall not propagate out of any
// imported subroutine. Undefined behavior can result if an exception crosses
// the language boundary from C++ into SystemVerilog."
//
// Two of those three sentences ask nothing of a simulator. The second binds
// whoever writes the C++, and no SystemVerilog tool can verify that a foreign
// body catches what it throws. The third grants the tool its latitude outright:
// where an exception does cross, the behaviour is undefined, so there is no
// outcome a conforming implementation could be held to.
//
// The first sentence is the one a tool can fail, and it fails as a build
// setting rather than as a line of code. An imported subroutine written in C++
// that throws and catches within itself observes the clause exactly -- nothing
// propagates out -- and it can only do so where the call path it runs on
// supports exceptions. Compiled with exceptions disabled, such a body calls
// std::terminate at the throw instead of returning, and implementing an import
// in C++ stops being possible. These cases are what would notice.
//
// Which C linkage conventions the boundary observes is §35.3.2's question and
// Annex H's answer, not this subclause's.
namespace {

// §35.5.1.6: an imported subroutine implemented in C++ may use exceptions
// within itself, so long as none escapes. The body throws and catches its own
// exception and returns normally, which is the arrangement the clause permits.
TEST(DpiCppImplementation, AnImportedSubroutineMayThrowAndCatchWithinItself) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_guarded";
  func.sv_name = "sv_guarded";
  func.return_type = DataTypeKind::kInt;
  func.impl = [](const std::vector<DpiArgValue>&) {
    int32_t answer = 0;
    try {
      throw std::runtime_error("handled inside the imported subroutine");
    } catch (const std::runtime_error&) {
      answer = 42;
    }
    return DpiArgValue::FromInt(answer);
  };
  rt.RegisterImport(func);

  // 42 is reached only through the catch, so the value says the throw happened
  // and was handled where the clause requires it to be.
  EXPECT_EQ(rt.CallImport("sv_guarded", {}).AsInt(), 42);
}

// §35.5.1.6: the C++ an imported subroutine is implemented in behaves as C++,
// so an exception caught within the body still unwinds the locals it passed on
// the way. The guard's destructor is what records that it did, and the result
// carries the value the body computed after catching, so the case fails if the
// unwinding or the return went wrong rather than only if the throw did.
TEST(DpiCppImplementation, AnExceptionCaughtWithinAnImportUnwindsItsLocals) {
  DpiRuntime rt;
  bool unwound = false;

  struct Guard {
    bool* flag;
    ~Guard() { *flag = true; }
  };

  DpiRtFunction func;
  func.c_name = "c_unwind";
  func.sv_name = "sv_unwind";
  func.return_type = DataTypeKind::kInt;
  func.impl = [&unwound](const std::vector<DpiArgValue>&) {
    int32_t answer = 0;
    try {
      Guard guard{&unwound};
      throw std::runtime_error("thrown past a local with a destructor");
    } catch (const std::runtime_error&) {
      answer = 7;
    }
    return DpiArgValue::FromInt(answer);
  };
  rt.RegisterImport(func);

  const DpiArgValue kResult = rt.CallImport("sv_unwind", {});

  EXPECT_TRUE(unwound);
  EXPECT_EQ(kResult.AsInt(), 7);
}

}  // namespace
