#include <gtest/gtest.h>

#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

// §6.9.2 vector net accessibility: the advisory keywords vectored and scalared
// govern how the PLI reports a vector net's expansion. These tests observe the
// production vpi_get mapping of the VpiObject accessibility flags onto the
// vpiExplicitScalared/vpiExplicitVectored/vpiExpanded properties.

// "the PLI shall consider the net expanded" for a scalared net: the explicit
// scalared property is true and the net reports as expanded.
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

// A vectored net is reported with the explicit vectored property set and is
// considered unexpanded by the PLI.
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

// A net declared with neither keyword carries no explicit accessibility and
// defaults to expanded.
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
