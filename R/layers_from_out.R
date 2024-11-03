layers_from_out <- function(raster, out_file) {
  options(warn = -1)
  # Read lines from .out file
  lines <- readLines(out_file)
  lines <- lines[-(1:7)]
  # Identify sections for each data category
  layer_starts <- grep("TOTAL RECORDS/CELL|NUMBER OF SPECIES/CELL|NUMBER OF SPECIES/CELL, including assumed records", lines)
  
  # Loop through each layer, read data, and assign to raster
  for (i in seq_along(layer_starts)) {
    # Get the layer name
    layer_name <- strsplit(lines[layer_starts[i]], ":")[[1]][1]
    
    # Read subsequent lines for the data values, until empty line or new section
    data_start <- layer_starts[i] + 2
    data_end <- layer_starts[i] + (nrow(raster)+1)
    data_lines <- lines[data_start:data_end]
    
    # Remove the first item of each line in data_lines
    cleaned_data_lines <- lapply(data_lines, function(line) {
      items <- unlist(strsplit(line, "\\s+"))
      items[-(1:2)]  # Remove the first two elements (row and column indices)
    })
    
    # Process data values into matrix
    values <- as.numeric(unlist(cleaned_data_lines)) |> na.exclude()
    values_matrix <- matrix(values, nrow = nrow(raster), ncol = ncol(raster), byrow = TRUE)
    
    # Create a new raster layer from values_matrix
    layer_rast <- rast(values_matrix, crs = crs(raster), extent = ext(raster))
    
    # Combine with existing raster
    raster <- c(raster, layer_rast)
  }
  
  names(raster) <- c("Total Records/Cell","Number of Species/Cell","Number of Species/Cell, including assumed records")
  
  return(raster)
}
