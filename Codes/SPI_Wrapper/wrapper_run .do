vlib work

vlog slave_RAM_intf.sv RAM.sv slave.sv wrapper_intf.sv wrapper_pkg.sv wrapper.sv wrapper_tb.sv wrapper_top.sv +define+SIM_RAM +define+SIM_SLAVE +define+SIM_WRAPPER +cover

vsim -voptargs=+acc work.wrapper_top -cover -sv_seed random

add wave *

coverage save SPI_cv.ucdb -onexit

run -all
