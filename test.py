original = [1, 2, 3,5, 4]
start_index = 2  # the index from which you want to start deleting
num_elements_to_delete = 2  # number of consecutive elements to delete

# Use slicing to create a new list excluding the elements to be deleted
modified = original[:start_index] + original[start_index + num_elements_to_delete:]

print(modified)  