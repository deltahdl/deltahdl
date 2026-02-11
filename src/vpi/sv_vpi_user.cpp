// IEEE 1800-2023 Annex M — sv_vpi_user.h implementation.

#include "vpi/sv_vpi_user.h"

vpiHandle vpi_register_assertion_cb(vpiHandle assertion, PLI_INT32 reason,
                                    vpi_assertion_callback_func cb_rtn,
                                    PLI_BYTE8* user_data) {
  (void)assertion;
  (void)reason;
  (void)cb_rtn;
  (void)user_data;
  return nullptr;
}
