#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.3.3 (Object file and line properties) states that most objects carry two
// location properties not drawn in the data model diagrams: vpiLineNo, read as
// an integer through vpi_get(), and vpiFile, read as a string through
// vpi_get_str(). They apply to every object that corresponds to something in
// the source text, with one fixed set of exceptions - object kinds that have no
// single source line or file: vpiCallback, vpiDelayTerm, vpiDelayDevice,
// vpiInterModPath, vpiIterator, vpiTimeQueue, vpiGenScopeArray, and
// vpiGenScope. (The `line directive of §22.12 may shift the reported values;
// that effect is §22.12's to define, not §37.3.3's.) These tests drive the
// production routines through the public C entry points, exactly as a PLI
// program would, by installing a private context as the global one.
class VpiFileAndLineProperty : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext ctx_;
};

// Claim: an object that corresponds to source text reports its source line
// through vpi_get(vpiLineNo).
TEST_F(VpiFileAndLineProperty, GetLineNoReturnsTheObjectsSourceLine) {
  VpiObject net;
  net.type = vpiNet;
  net.line_no = 42;

  EXPECT_EQ(vpi_get(vpiLineNo, &net), 42);
}

// Claim: an object that corresponds to source text reports its source file
// through vpi_get_str(vpiFile).
TEST_F(VpiFileAndLineProperty, GetStrFileReturnsTheObjectsSourceFile) {
  VpiObject reg;
  reg.type = vpiReg;
  reg.file = "design.sv";

  const char* file = vpi_get_str(vpiFile, &reg);
  ASSERT_NE(file, nullptr);
  EXPECT_EQ(std::string(file), "design.sv");
}

// Claim (exception): vpiLineNo does not apply to the object kinds §37.3.3
// lists, so vpi_get(vpiLineNo) on each of them is not a valid query and yields
// vpiUndefined - even when a line was nonetheless stored on the object.
TEST_F(VpiFileAndLineProperty, ExceptedKindsHaveNoLineNo) {
  const int kExcepted[] = {vpiCallback,      vpiDelayTerm, vpiDelayDevice,
                           vpiInterModPath,  vpiIterator,  vpiTimeQueue,
                           vpiGenScopeArray, vpiGenScope};
  for (int type : kExcepted) {
    VpiObject obj;
    obj.type = type;
    obj.line_no =
        99;  // present in the model, but not a valid query for this kind
    EXPECT_EQ(vpi_get(vpiLineNo, &obj), vpiUndefined)
        << "object type " << type << " must not report a vpiLineNo";
  }
}

// Claim (exception): vpiFile likewise does not apply to the listed kinds, so
// vpi_get_str(vpiFile) yields null on each of them regardless of any file
// string stored on the object.
TEST_F(VpiFileAndLineProperty, ExceptedKindsHaveNoFile) {
  const int kExcepted[] = {vpiCallback,      vpiDelayTerm, vpiDelayDevice,
                           vpiInterModPath,  vpiIterator,  vpiTimeQueue,
                           vpiGenScopeArray, vpiGenScope};
  for (int type : kExcepted) {
    VpiObject obj;
    obj.type = type;
    obj.file = "ignored.sv";  // stored, yet not reportable for this kind
    EXPECT_EQ(vpi_get_str(vpiFile, &obj), nullptr)
        << "object type " << type << " must not report a vpiFile";
    EXPECT_FALSE(VpiHasLocationProperties(type));
  }
}

// -----------------------------------------------------------------------------
// §37.3.3 against a design. The cases above stamp a line and a file onto an
// object by hand and read them back, which says what vpi_get() and
// vpi_get_str() do with an object that carries them; it says nothing about an
// object of an elaborated design carrying them at all. Nothing under src/ ever
// wrote either property, so every net, variable and port of every design
// answered zero and NULL, and "applicable to every object that corresponds to
// some object within the source code" held for no object of any design.
// -----------------------------------------------------------------------------

// What the application read. A calltf is a plain C function with no return path
// to the case that provoked it, and vpi_get_str hands back one buffer every
// call reuses (§38.11), so the file is copied as it is read.
int g_net_line = 0;
std::string g_net_file;
int g_var_line = 0;
int g_top_net_line = 0;
int g_port_line = 0;

int ReadLocationsCalltf(const char*) {
  vpiHandle net = vpi_handle_by_name("m1.w", nullptr);
  if (net != nullptr) {
    g_net_line = vpi_get(vpiLineNo, net);
    const char* file = vpi_get_str(vpiFile, net);
    if (file != nullptr) g_net_file = file;
  }
  vpiHandle var = vpi_handle_by_name("m1.r", nullptr);
  if (var != nullptr) g_var_line = vpi_get(vpiLineNo, var);
  vpiHandle top_net = vpi_handle_by_name("top_sig", nullptr);
  if (top_net != nullptr) g_top_net_line = vpi_get(vpiLineNo, top_net);

  vpiHandle mod = vpi_handle_by_name("m1", nullptr);
  if (mod == nullptr) return 0;
  vpiHandle itr = vpi_iterate(vpiPort, mod);
  if (itr == nullptr) return 0;
  vpiHandle port = vpi_scan(itr);
  if (port != nullptr) g_port_line = vpi_get(vpiLineNo, port);
  while (vpi_scan(itr) != nullptr) {
  }
  return 0;
}

void RegisterLocationProbe() {
  g_net_line = 0;
  g_net_file.clear();
  g_var_line = 0;
  g_top_net_line = 0;
  g_port_line = 0;

  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = "$probe";
  data.calltf = &ReadLocationsCalltf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);
}

// A design whose declarations stand on lines the case can name: the port on
// line 1, the net on line 2 and the variable on line 3 of the instantiated
// module, and a net of the top on line 6.
void RunADesignOfLocatedDeclarations(SimFixture& f) {
  auto* design = ElaborateSrc(
      "module m(input a);\n"
      "  wire w;\n"
      "  reg r;\n"
      "endmodule\n"
      "module t;\n"
      "  wire top_sig;\n"
      "  m m1(top_sig);\n"
      "  initial $probe;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
}

class VpiLocationInARun : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

// §37.3.3: a net corresponds to its declaration in the source text, so the
// object the design built for it reports the line that declaration stands on.
TEST_F(VpiLocationInARun, ADeclaredNetReportsItsOwnLine) {
  RegisterLocationProbe();

  SimFixture f;
  RunADesignOfLocatedDeclarations(f);

  EXPECT_EQ(g_net_line, 2);
}

// §37.3.3: vpiFile is the other half of the same location, and it names the
// file the declaration was read from rather than any identifier this tool
// assigned it.
TEST_F(VpiLocationInARun, ADeclaredNetReportsTheFileItWasDeclaredIn) {
  RegisterLocationProbe();

  SimFixture f;
  RunADesignOfLocatedDeclarations(f);

  EXPECT_EQ(g_net_file, "<test>");
}

// §37.3.3 applies to "every object that corresponds to some object within the
// source code", which a variable declaration does as much as a net one. The
// two stand on different lines, so a variable reporting the net's line would
// pass a case that only asked whether some line came back.
TEST_F(VpiLocationInARun, ADeclaredVariableReportsItsOwnLine) {
  RegisterLocationProbe();

  SimFixture f;
  RunADesignOfLocatedDeclarations(f);

  EXPECT_EQ(g_var_line, 3);
}

// §37.3.3: a port is written in the source text too, and this one stands in the
// module header a line above the net and two above the variable.
TEST_F(VpiLocationInARun, ADeclaredPortReportsItsOwnLine) {
  RegisterLocationProbe();

  SimFixture f;
  RunADesignOfLocatedDeclarations(f);

  EXPECT_EQ(g_port_line, 1);
}

// §37.3.3: a declaration of the top module is reached under its bare name,
// with no instance path over it, and reports its line the same way.
TEST_F(VpiLocationInARun, ANetOfTheTopModuleReportsItsOwnLine) {
  RegisterLocationProbe();

  SimFixture f;
  RunADesignOfLocatedDeclarations(f);

  EXPECT_EQ(g_top_net_line, 6);
}

}  // namespace
}  // namespace delta
