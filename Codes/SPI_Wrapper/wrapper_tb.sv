import wrapper_pkg::*;

module wrapper_tb (wrapper_intf.TEST W_intf);
	localparam MEM_DEPTH = W_intf.MEM_DEPTH;
	localparam ADDR_SIZE = $clog2(MEM_DEPTH);

	typedef enum bit [2 : 0] {IDLE, CHK_CMD, WRITE, READ_ADD, READ_DATA} STATE_e;
	
    logic clk, rst_n, SS_n, MOSI, MISO;

    assign clk          = W_intf.clk;
    assign W_intf.rst_n = rst_n;
    assign W_intf.SS_n  = SS_n;
    assign W_intf.MOSI  = MOSI;
	assign MISO         = W_intf.MISO;  

	STATE_e cs_ref;
	logic MISO_ref;
	bit [ADDR_SIZE + 1 : 0] rx_data_ref;
	bit [$clog2(ADDR_SIZE) : 0] count_rx_ref, count_tx_ref;
	bit rd_flag_ref, rx_valid_in_RD, rx_valid_ref, tx_valid_ref;
	logic [ADDR_SIZE - 1 : 0] mem_ref [MEM_DEPTH - 1 : 0];
	bit [ADDR_SIZE - 1 : 0] wa_ref, ra_ref, tx_data_ref;

    wrapper_tr #(.MEM_DEPTH(MEM_DEPTH)) tr;

	always @(posedge clk) 
        tr.cvgrp.sample();

    initial begin
		tr = new();
		#0
		$readmemh("RAM_data.dat", mem_ref, 0, 255);

		check_rst;

		repeat (10000) begin
			slave_ra:	assert (tr.randomize());
			rst_n 	 = tr.rst_n;
			SS_n 	 = tr.SS_n;
			MOSI     = tr.MOSI;
			check_result(rst_n, SS_n, MOSI);
		end
		$stop;
    end

	task ref_model (input logic rst_n, SS_n, MOSI);
		// rx_data && MISO
		if (!rst_n) begin
			cs_ref = IDLE;
			count_rx_ref   = ADDR_SIZE + 2;
			count_tx_ref   = ADDR_SIZE;
			rd_flag_ref    = 0;
			rx_data_ref    = 0;
			rx_valid_in_RD = 0;
			MISO_ref       = 0;
			tx_valid_ref   = 0;
			rx_valid_ref   = 0;  
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
					else if ((count_tx_ref != 0) && (tx_valid_ref)) begin
						MISO_ref = tx_data_ref [count_tx_ref - 1];
						count_tx_ref--;
					end
				end
			endcase 
		end

		// RAM
		if (!rst_n) begin
			wa_ref 	       = 0;
			ra_ref         = 0;
			tx_data_ref    = 0;
			tx_valid_ref   = 0;
		end
		else if (rx_valid_ref) begin
			case (rx_data_ref [ADDR_SIZE + 1 : ADDR_SIZE])
				2'b00:	wa_ref 	  		  = rx_data_ref [ADDR_SIZE - 1 : 0];						
				2'b01:	mem_ref [wa_ref]  = rx_data_ref [ADDR_SIZE - 1 : 0];
				2'b10:	ra_ref 	          = rx_data_ref [ADDR_SIZE - 1 : 0];
				2'b11:  tx_data_ref 	  = mem_ref [ra_ref];
			endcase
			tx_valid_ref = (&(rx_data_ref [ADDR_SIZE + 1 : ADDR_SIZE]));
		end

		// rx_valid
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
			$error ("Check_rst failed: rst_n = %0b, MISO = %0b, time = %0t", rst_n, MISO, $time());
	endtask //

	task check_result (input logic rst_n, SS_n, MOSI);
		@(negedge clk);
		ref_model(rst_n, SS_n, MOSI);

		chk_result_MISO_a: assert (MISO == MISO_ref) 
		else
			$error ("Check_result failed: rst_n = %0b, SS_n = %0b, MOSI = %0b, MISO = %0d, MISO_ref = %0d, time = %0t",
			 rst_n, SS_n, MOSI, MISO, MISO_ref, $time());
	endtask //
endmodule