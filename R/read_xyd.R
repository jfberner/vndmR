read_xyd <- function(file_path) {
  # Read the file
  file_content <- readLines(file_path)
  
  # Clean empty strings at the beginning
  file_content <- file_content[file_content != ""]
  
  # Get the indexes of the strings that start with "sp"
  sp_indexes <- grep("^sp", file_content)
  
  # remove the entry for the number of species
  sp_indexes <- sp_indexes[-1]
  
  # Initialize a list to store the data
  data_list <- list()
  
  # Process the file content
  for (i in 1:length(sp_indexes)) {
    sp_index <- sp_indexes[i]
    species_name <- gsub("sp", "", file_content[sp_index]) # Extract the number inside the string
    species_name <- gsub("\\[|\\]", "", species_name) # Extract the content inside "[]"
    
    # Get the index of the next "sp" or "map" string
    next_index <- if (i == length(sp_indexes)) {
      # For the last species, use the "map" string
      grep("^map", file_content)
    } else {
      # For other species, use the next "sp" string
      sp_indexes[i + 1]
    }
    
    # Get the coordinate strings
    coord_strings <- paste(file_content[(sp_index + 1):(next_index - 1)], collapse = ",")
    
    # Create a data frame for this species
    species_df <- data.frame(sp_index = paste0("sp ", str_extract(species_name, "\\d+")), species = trimws(str_extract_all(trimws(species_name), "\\D+")), coords = coord_strings)
    
    # Add the data frame to the list
    data_list <- append(data_list, list(species_df))
  }
  
  # Combine all species data frames into one data frame
  species_df <- do.call(rbind, data_list)
  
  # Convert species_df to an sf object
  species_sf <- species_df
  out_df <- tibble()
  
  for (j in 1:length(species_df$coords)) {
    temp_sf <- strsplit(species_df$coords[j], ",")[[1]]
    temp_sf1 <- do.call(rbind, strsplit(temp_sf, " ")) |> as.data.frame()
    names(temp_sf1) <- c('x','y')
    temp_sf2 <- st_as_sf(temp_sf1, coords = c('y', 'x')) |> aggregate(temp_sf1, st_point) |> bind_cols(species_sf[j,1:2]) |> select(-x,-y)
    out_df <- rbind(out_df, temp_sf2)
  }

  final_sf <- out_df |> group_by(species, sp_index) |> summarise(do_union = T)
  st_crs(final_sf) <- st_crs('EPSG:4326')
  
  return(final_sf)
}