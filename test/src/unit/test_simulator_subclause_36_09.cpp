#include <gtest/gtest.h>

#include <algorithm>
#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §36.9 -- PLI mechanism. "The PLI mechanism provides a means to have PLI
// applications called for various reasons when the associated system task and
// system function $ name is encountered in the SystemVerilog source
// description. For example, when a SystemVerilog simulator first compiles the
// SystemVerilog source description, a specific compiletf PLI routine can be
// called that performs syntax checking to verify the user-defined system task
// or system function is being used correctly. Then, as simulation is executing,
// a specific calltf PLI routine can be called to perform the operations
// required by the PLI application. User-defined system tasks and system
// functions, and their associated routines and data, are defined by registering
// system task and system function callbacks."
//
// What the clause states is the mechanism rather than any one of its parts:
// that a registration is what defines a name, its routines and its data, and
// that the name written in the source is what reaches them, for more than one
// reason and at more than one point in the tool's life. §36.8 fixes what those
// points are and §36.9.1 what a registration is; the cases here are the
// connection between the two, which is that a $ name standing in the source
// description reaches the registration's applications at all.

// What the applications recorded across a run, in the order they ran. A PLI
// application is a plain C function with no return path to the case that
// provoked it, so file scope is the only place it has to leave this.
std::vector<std::string> g_reached;
const char* g_probe_user_data_seen = nullptr;

char g_probe_user_data[] = "probe-data";
char g_other_user_data[] = "other-data";

int ProbeCompiletf(const char* user_data) {
  g_reached.emplace_back("probe-compiletf");
  g_probe_user_data_seen = user_data;
  return 0;
}

int ProbeCalltf(const char* user_data) {
  g_reached.emplace_back("probe-calltf");
  g_probe_user_data_seen = user_data;
  return 0;
}

int OtherCompiletf(const char*) {
  g_reached.emplace_back("other-compiletf");
  return 0;
}

int OtherCalltf(const char*) {
  g_reached.emplace_back("other-calltf");
  return 0;
}

// Registers $probe, which is the name every design below writes.
void RegisterProbe() {
  s_vpi_systf_data data = {};
  data.type = vpiSysFunc;
  data.tfname = "$probe";
  data.compiletf = &ProbeCompiletf;
  data.calltf = &ProbeCalltf;
  data.user_data = g_probe_user_data;
  ASSERT_NE(vpi_register_systf(&data), nullptr);
}

// Registers $other, which no design below writes. It carries its own routines
// and its own data so that a run reaching them would say so.
void RegisterOther() {
  s_vpi_systf_data data = {};
  data.type = vpiSysFunc;
  data.tfname = "$other";
  data.compiletf = &OtherCompiletf;
  data.calltf = &OtherCalltf;
  data.user_data = g_other_user_data;
  ASSERT_NE(vpi_register_systf(&data), nullptr);
}

class PliMechanism : public ::testing::Test {
 protected:
  void SetUp() override {
    g_reached.clear();
    g_probe_user_data_seen = nullptr;
    SetGlobalVpiContext(&vpi_ctx_);
  }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

// §36.9: the applications are called "for various reasons", and the clause's
// own example names two of them in order -- a compiletf "when a SystemVerilog
// simulator first compiles the SystemVerilog source description", and "then, as
// simulation is executing", a calltf. One name written once in the source is
// what reaches both.
TEST_F(PliMechanism,
       TheNameInTheSourceReachesApplicationsForMoreThanOneReason) {
  RegisterProbe();

  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int r;\n"
      "  initial r = $probe();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  // The whole sequence rather than two counts, because the clause puts the two
  // reasons in an order: the compile comes first and the execution after it.
  EXPECT_EQ(g_reached,
            (std::vector<std::string>{"probe-compiletf", "probe-calltf"}));
}

// §36.9: "User-defined system tasks and system functions, and their associated
// routines and data, are defined by registering system task and system function
// callbacks." So which applications a name reaches is decided by the
// registration that named it, and a second registration standing in the same
// run is not what the source's name reaches. Its routines are distinct from
// $probe's and would name themselves if they ran.
TEST_F(PliMechanism, TheRoutinesAndTheDataComeFromTheRegistrationOfThatName) {
  RegisterProbe();
  RegisterOther();

  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int r;\n"
      "  initial r = $probe();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  EXPECT_EQ(g_reached,
            (std::vector<std::string>{"probe-compiletf", "probe-calltf"}));
  // The data is the registration's too, and it is $probe's rather than the
  // other registration's.
  EXPECT_EQ(g_probe_user_data_seen, g_probe_user_data);
}

// §36.9: the applications are reached "when the associated system task and
// system function $ name is encountered in the SystemVerilog source
// description", which says where the name stands and not which construct holds
// it. §6.8's declaration initializer is one of the places the source writes
// one, and the build period walked processes and continuous assignments and no
// declaration at all, so a name written here was encountered by the design and
// by nothing that called an application for it.
TEST_F(PliMechanism, ANameEncounteredInADeclarationReachesItsApplications) {
  RegisterProbe();

  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int r = $probe();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  // Both reasons are reached, which is what the case is about. The order is not
  // asserted: this simulator performs §6.8's static initialization while it
  // builds the design rather than at time zero, so the calltf for a declaration
  // initializer runs inside the build rather than after it, and that is a
  // question about when initialization happens rather than about §36.9.
  EXPECT_EQ(std::count(g_reached.begin(), g_reached.end(), "probe-compiletf"),
            1);
  EXPECT_EQ(std::count(g_reached.begin(), g_reached.end(), "probe-calltf"), 1);
}

}  // namespace
}  // namespace delta
