grid_from_dat <- function(dat_file) {
  # Read lines from .dat file
  lines <- readLines(dat_file)
  
  # Extract grid information from the head of the file
  gridx_line <- grep("gridx", lines, value = TRUE)
  gridy_line <- grep("gridy", lines, value = TRUE)
  rows_line <- grep("rows", lines, value = TRUE)
  cols_line <- grep("cols", lines, value = TRUE)
  
  # Parse grid parameters
  x_start <- as.numeric(strsplit(gridx_line, "\\s+")[[1]][2])
  x_res <- as.numeric(strsplit(gridx_line, "\\s+")[[1]][3])
  y_start <- as.numeric(strsplit(gridy_line, "\\s+")[[1]][2])
  y_res <- as.numeric(strsplit(gridy_line, "\\s+")[[1]][3])
  nrows <- as.integer(strsplit(rows_line, "\\s+")[[1]][2])
  ncols <- as.integer(strsplit(cols_line, "\\s+")[[1]][2])
  
  # Initialize empty raster in terra
  r <- rast(nrows = nrows, ncols = ncols, 
            xmin = x_start, 
            xmax = x_start + (ncols * x_res), 
            ymin = if(y_start < 0)  y_start - (nrows * y_res) else y_start, 
            ymax = if( y_start < 0 ) y_start else y_start - (nrows * y_res),
            crs = "EPSG:4326")
  
  return(r)
}
