

#ifndef VPI_COMPATIBILITY_H
#define VPI_COMPATIBILITY_H

/*
 * Clause 36.12.2.1 -- Mechanism 1: compile-based binding to a compatibility
 * mode. An application selects a prior-standard VPI compatibility mode by
 * defining one of the version symbols below before the standard VPI include
 * files are processed (either with a "#define ... 1" or a "-D" on the compiler
 * command line). Selecting a mode retargets the standard VPI entry points to
 * mode-specific variants so that a recompiled application observes the data
 * model of that earlier standard version.
 */

/*
 * At most one compatibility version symbol may be selected. Defining more than
 * one for the same application is a compile-time error. The count is taken over
 * the eight selectable symbols exactly as the application defined them, before
 * any internal version chaining performed below, so that selecting a single
 * version never trips the check.
 */
#if (defined(VPI_COMPATIBILITY_VERSION_1364v1995) + \
     defined(VPI_COMPATIBILITY_VERSION_1364v2001) + \
     defined(VPI_COMPATIBILITY_VERSION_1364v2005) + \
     defined(VPI_COMPATIBILITY_VERSION_1800v2005) + \
     defined(VPI_COMPATIBILITY_VERSION_1800v2009) + \
     defined(VPI_COMPATIBILITY_VERSION_1800v2012) + \
     defined(VPI_COMPATIBILITY_VERSION_1800v2017) + \
     defined(VPI_COMPATIBILITY_VERSION_1800v2023)) > 1
#error "At most one VPI_COMPATIBILITY_VERSION_* symbol may be defined"
#endif

#ifdef VPI_COMPATIBILITY_VERSION_1800v2023
#define VPI_COMPATIBILITY_VERSION_1800v2012
#endif

#ifdef VPI_COMPATIBILITY_VERSION_1800v2017
#define VPI_COMPATIBILITY_VERSION_1800v2012
#endif

#ifdef VPI_COMPATIBILITY_VERSION_1364v1995
#define vpi_compare_objects vpi_compare_objects_1364v1995
#define vpi_control vpi_control_1364v1995
#define vpi_get vpi_get_1364v1995
#define vpi_get_str vpi_get_str_1364v1995
#define vpi_get_value vpi_get_value_1364v1995
#define vpi_handle vpi_handle_1364v1995
#define vpi_handle_by_index vpi_handle_by_index_1364v1995
#define vpi_handle_by_multi_index vpi_handle_by_multi_index_1364v1995
#define vpi_handle_by_name vpi_handle_by_name_1364v1995
#define vpi_handle_multi vpi_handle_multi_1364v1995
#define vpi_iterate vpi_iterate_1364v1995
#define vpi_put_value vpi_put_value_1364v1995
#define vpi_register_cb vpi_register_cb_1364v1995
#define vpi_scan vpi_scan_1364v1995
#endif

#ifdef VPI_COMPATIBILITY_VERSION_1364v2001
#define vpi_compare_objects vpi_compare_objects_1364v2001
#define vpi_control vpi_control_1364v2001
#define vpi_get vpi_get_1364v2001
#define vpi_get_str vpi_get_str_1364v2001
#define vpi_get_value vpi_get_value_1364v2001
#define vpi_handle vpi_handle_1364v2001
#define vpi_handle_by_index vpi_handle_by_index_1364v2001
#define vpi_handle_by_multi_index vpi_handle_by_multi_index_1364v2001
#define vpi_handle_by_name vpi_handle_by_name_1364v2001
#define vpi_handle_multi vpi_handle_multi_1364v2001
#define vpi_iterate vpi_iterate_1364v2001
#define vpi_put_value vpi_put_value_1364v2001
#define vpi_register_cb vpi_register_cb_1364v2001
#define vpi_scan vpi_scan_1364v2001
#endif

#ifdef VPI_COMPATIBILITY_VERSION_1364v2005
#define vpi_compare_objects vpi_compare_objects_1364v2005
#define vpi_control vpi_control_1364v2005
#define vpi_get vpi_get_1364v2005
#define vpi_get_str vpi_get_str_1364v2005
#define vpi_get_value vpi_get_value_1364v2005
#define vpi_handle vpi_handle_1364v2005
#define vpi_handle_by_index vpi_handle_by_index_1364v2005
#define vpi_handle_by_multi_index vpi_handle_by_multi_index_1364v2005
#define vpi_handle_by_name vpi_handle_by_name_1364v2005
#define vpi_handle_multi vpi_handle_multi_1364v2005
#define vpi_iterate vpi_iterate_1364v2005
#define vpi_put_value vpi_put_value_1364v2005
#define vpi_register_cb vpi_register_cb_1364v2005
#define vpi_scan vpi_scan_1364v2005
#endif

#ifdef VPI_COMPATIBILITY_VERSION_1800v2005
#define vpi_compare_objects vpi_compare_objects_1800v2005
#define vpi_control vpi_control_1800v2005
#define vpi_get vpi_get_1800v2005
#define vpi_get_str vpi_get_str_1800v2005
#define vpi_get_value vpi_get_value_1800v2005
#define vpi_handle vpi_handle_1800v2005
#define vpi_handle_by_index vpi_handle_by_index_1800v2005
#define vpi_handle_by_multi_index vpi_handle_by_multi_index_1800v2005
#define vpi_handle_by_name vpi_handle_by_name_1800v2005
#define vpi_handle_multi vpi_handle_multi_1800v2005
#define vpi_iterate vpi_iterate_1800v2005
#define vpi_put_value vpi_put_value_1800v2005
#define vpi_register_cb vpi_register_cb_1800v2005
#define vpi_scan vpi_scan_1800v2005
#endif

#ifdef VPI_COMPATIBILITY_VERSION_1800v2009
#define vpi_compare_objects vpi_compare_objects_1800v2009
#define vpi_control vpi_control_1800v2009
#define vpi_get vpi_get_1800v2009
#define vpi_get_str vpi_get_str_1800v2009
#define vpi_get_value vpi_get_value_1800v2009
#define vpi_handle vpi_handle_1800v2009
#define vpi_handle_by_index vpi_handle_by_index_1800v2009
#define vpi_handle_by_multi_index vpi_handle_by_multi_index_1800v2009
#define vpi_handle_by_name vpi_handle_by_name_1800v2009
#define vpi_handle_multi vpi_handle_multi_1800v2009
#define vpi_iterate vpi_iterate_1800v2009
#define vpi_put_value vpi_put_value_1800v2009
#define vpi_register_cb vpi_register_cb_1800v2009
#define vpi_scan vpi_scan_1800v2009
#endif

#ifdef VPI_COMPATIBILITY_VERSION_1800v2012
#define vpi_compare_objects vpi_compare_objects_1800v2012
#define vpi_control vpi_control_1800v2012
#define vpi_get vpi_get_1800v2012
#define vpi_get_str vpi_get_str_1800v2012
#define vpi_get_value vpi_get_value_1800v2012
#define vpi_handle vpi_handle_1800v2012
#define vpi_handle_by_index vpi_handle_by_index_1800v2012
#define vpi_handle_by_multi_index vpi_handle_by_multi_index_1800v2012
#define vpi_handle_by_name vpi_handle_by_name_1800v2012
#define vpi_handle_multi vpi_handle_multi_1800v2012
#define vpi_iterate vpi_iterate_1800v2012
#define vpi_put_value vpi_put_value_1800v2012
#define vpi_register_cb vpi_register_cb_1800v2012
#define vpi_scan vpi_scan_1800v2012
#endif

#endif
