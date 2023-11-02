import slave_pkg::*;

module slave_tb (
    input logic MISO, 
	slave_RAM_intf.SLAVE_test SR_intf,
	output logic SS_n, MOSI
);
    localparam MEM_DEPTH = SR_intf.MEM_DEPTH;
	localparam ADDR_SIZE = $clog2(MEM_DEPTH);

	typedef enum bit [2 : 0] {IDLE, CHK_CMD, WRITE, READ_ADD, READ_DATA} STATE_e;
	
	logic clk, rst_n, tx_valid, rx_valid;
	logic [ADDR_SIZE - 1 : 0] tx_data;
	logic [ADDR_SIZE + 1 : 0] rx_data;

	assign clk 				= SR_intf.clk;
	assign SR_intf.rst_n 	= rst_n;
	assign SR_intf.tx_valid = tx_valid;
	assign SR_intf.tx_data 	= tx_data;
	assign rx_valid 	    = SR_intf.rx_valid;
	assign rx_data 		    = SR_intf.rx_data;

	STATE_e cs_ref;
	logic rx_valid_ref, MISO_ref;
	logic [ADDR_SIZE + 1 : 0] rx_data_ref;
	bit [$clog2(ADDR_SIZE) : 0] count_rx_ref, count_tx_ref;
	bit rd_flag_ref, rx_valid_in_RD;

	slave_tr #(.MEM_DEPTH(MEM_DEPTH)) tr;

	always @(posedge clk) 
        tr.cvgrp.sample();

    initial begin
		tr = new();
		#0
		check_rst;

		repeat (10000) begin
			slave_ra:	assert (tr.randomize());
			rst_n 	 = tr.rst_n;
			SS_n 	 = tr.SS_n;
			MOSI     = tr.MOSI;
			tx_valid = tr.tx_valid;
			tx_data  = tr.tx_data;
			check_result(rst_n, SS_n, MOSI, tx_valid, tx_data);
		end
		$stop;
    end

	function string stim2str (input logic rst_n, SS_n, MOSI, tx_valid, input logic [ADDR_SIZE - 1 : 0] tx_data);
		stim2str = $sformatf("rst_n = %0b, SS_n = %0b, MOSI = %0b, tx_valid = %0b, tx_data = %0d", rst_n, SS_n, MOSI, tx_valid, tx_data);
	endfunction //

	task ref_model (input logic rst_n, SS_n, MOSI, tx_valid, input logic [ADDR_SIZE - 1 : 0] tx_data);
		if (!rst_n) begin
			cs_ref         = IDLE;
			count_rx_ref   = ADDR_SIZE + 2;
			count_tx_ref   = ADDR_SIZE;
			rd_flag_ref = 0;
			rx_data_ref    = 0;
			MISO_ref       = 0;
			rx_valid_in_RD = 0;
		end
		else begin
			case (cs_ref)
				IDLE: begin
					count_rx_ref = ADDR_SIZE + 2;
					count_tx_ref = ADDR_SIZE;
					rx_data_ref = 0;
					MISO_ref = 0;
					if (!SS_n)
						cs_ref = CHK_CMD;
				end
				CHK_CMD: begin
					if (SS_n)
						cs_ref = IDLE;
					else if (!MOSI)
						cs_ref = WRITE;
					else if (!rd_flag_ref)
						cs_ref = READ_ADD;
					else
						cs_ref = READ_DATA;
				end
				WRITE: begin
					if (SS_n) 
						cs_ref = IDLE;
					if (count_rx_ref != 0) begin
						rx_data_ref [count_rx_ref - 1] = MOSI;
						count_rx_ref--;
					end
				end
				READ_ADD: begin
					if (SS_n) begin
						cs_ref = IDLE;
						if (count_rx_ref == 0)
							rd_flag_ref = 1;
					end
					if (count_rx_ref != 0) begin
						rx_data_ref [count_rx_ref - 1] = MOSI;
						count_rx_ref--;
					end
				end
				READ_DATA: begin
					if (SS_n) begin
						cs_ref = IDLE;
						if (count_tx_ref == 0)
							rd_flag_ref = 0;
					end
					if (count_rx_ref != 0) begin
						rx_data_ref [count_rx_ref - 1] = MOSI;
						count_rx_ref--;
					end
					else if ((count_tx_ref != 0) && (tx_valid)) begin
						MISO_ref = tx_data [count_tx_ref - 1];
						count_tx_ref--;
					end
				end
			endcase 
		end
		rx_valid_ref = (((cs_ref == WRITE) || (cs_ref == READ_ADD) || ((cs_ref == READ_DATA) && (!rx_valid_in_RD))) && (count_rx_ref == 0));
		if (count_rx_ref == (ADDR_SIZE + 2))
			rx_valid_in_RD = 0;
		else if (count_rx_ref == 0)
			rx_valid_in_RD = 1;
	endtask //

	task check_rst;
		rst_n = 0;

		@(negedge clk);
		chk_rst_MISO_a: assert (MISO == 0) 
		else
			$error ("Check_rst failed for MISO: rst_n = %0b, MISO = %0b, time = %0t", rst_n, MISO, $time());
		
		chk_rst_rx_data_a: assert (rx_data == 0) 
		else
			$error ("Check_rst failed for rx_data: rst_n = %0b, rx_data = %0d, time = %0t", rst_n, rx_data, $time());
		
		chk_rst_rx_valid_a :assert (rx_valid == 0) 
		else
			$error ("Check_rst failed for rx_valid: rst_n = %0b, rx_valid = %0b, time = %0t", rst_n, rx_valid, $time());
	endtask //

	task check_result (input logic rst_n, SS_n, MOSI, tx_valid, input logic [ADDR_SIZE - 1 : 0] tx_data);
		@(negedge clk);
		ref_model(rst_n, SS_n, MOSI, tx_valid, tx_data);

		chk_result_MISO_a: assert (MISO == MISO_ref) 
		else
			$error ("Check_result failed for MISO: %0s, MISO = %0d, MISO_ref = %0d, time = %0t", 
			 stim2str(rst_n, SS_n, MOSI, tx_valid, tx_data), MISO, MISO_ref, $time());
			
		chk_result_rx_data_a: assert (rx_data == rx_data_ref) 
		else
			$error ("Check_result failed for rx_data: %0s, rx_data = %0d, rx_data_ref = %0d, time = %0t", 
			 stim2str(rst_n, SS_n, MOSI, tx_valid, tx_data), rx_data, rx_data_ref, $time());
			
		chk_result_rx_valid_a: assert (rx_valid == rx_valid_ref) 
		else
			$error ("Check_result failed for rx_valid: %0s, rx_valid = %0d, rx_valid_ref = %0d, time = %0t", 
			 stim2str(rst_n, SS_n, MOSI, tx_valid, tx_data), rx_valid, rx_valid_ref, $time());
	endtask //
endmodule