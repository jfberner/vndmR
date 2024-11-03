# Usage
dat_file <- "data/raw/sample_data/resultados_consenso/tmp.dat"
out_file <- "data/raw/sample_data/resultados_consenso/consensus.out"
xyd_file <- "data/raw/sample_data/species_xyd.xyd"

# Source
source('R/read_xyd.R')
source('R/grid_from_dat.R')
source('R/layers_from_out.R')

# Create raster and add layers
occurrences <- read_xyd(xyd_file)
grid <- grid_from_dat(dat_file)
raster_with_layers <- layers_from_out(grid, out_file)

# testing - do not run this in an old pc / with low memory
mapview::mapview(occurrences, zcol = 'species') +
mapview::mapview(raster_with_layers[[1]], alpha.regions = 0.1)

# next: get consensus maps imported. Each consensus has to be exported to an .acf fle which spits out EACH SQUARE with its value. Need to import each square in the grid, or actually find out which raster cell ir refers to and assign a value based on the index or something. Something for another day :)

# Hope this helps so far.