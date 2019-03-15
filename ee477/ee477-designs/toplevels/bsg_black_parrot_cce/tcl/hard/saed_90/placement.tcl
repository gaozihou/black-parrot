# placement.tcl
#
# This file contains information used by icc to specify placement of
# cell groups or blocks within the floorplan of the chip. This is quite
# difficult to make it prcess independant thus this file is in the
# hardened folder.
#
#   create_bounds -name <object_name> -coordinate { {<llx> <lly>} {<urx> <ury>} } -type <type = soft,hard,exclusive> -cycle_color { hierarchy_regex }
#

# TODO: Place any placement bounds below!

create_bounds -name top_bounds -coordinate {{440.445 1133.730} {2033.950 2087.720}} -type soft -cycle_color [remove_from_collection [get_cells -hier *] [all_macro_cells]]

