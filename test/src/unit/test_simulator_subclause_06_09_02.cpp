#include <gtest/gtest.h>

#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

TEST(VectorNetAccessibility, ScalaredNetIsExpandedToPli) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  VpiObject obj;
  obj.type = vpiNet;
  obj.is_scalared = true;

  EXPECT_EQ(vpi_get(vpiExplicitScalared, VpiHandleOf(&obj)), 1);
  EXPECT_EQ(vpi_get(vpiExplicitVectored, VpiHandleOf(&obj)), 0);
  EXPECT_EQ(vpi_get(vpiExpanded, VpiHandleOf(&obj)), 1);
}

TEST(VectorNetAccessibility, VectoredNetIsUnexpandedToPli) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  VpiObject obj;
  obj.type = vpiNet;
  obj.is_vectored = true;

  EXPECT_EQ(vpi_get(vpiExplicitVectored, VpiHandleOf(&obj)), 1);
  EXPECT_EQ(vpi_get(vpiExplicitScalared, VpiHandleOf(&obj)), 0);
  EXPECT_EQ(vpi_get(vpiExpanded, VpiHandleOf(&obj)), 0);
}

TEST(VectorNetAccessibility, PlainNetDefaultsToExpanded) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  VpiObject obj;
  obj.type = vpiNet;

  EXPECT_EQ(vpi_get(vpiExplicitScalared, VpiHandleOf(&obj)), 0);
  EXPECT_EQ(vpi_get(vpiExplicitVectored, VpiHandleOf(&obj)), 0);
  EXPECT_EQ(vpi_get(vpiExpanded, VpiHandleOf(&obj)), 1);
}

}  // namespace
}  // namespace delta
