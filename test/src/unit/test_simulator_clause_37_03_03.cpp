#include <gtest/gtest.h>

#include <string>

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

}  // namespace
}  // namespace delta
