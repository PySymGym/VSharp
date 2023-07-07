import logging

import pygad
import pygad.torchga
from torch.multiprocessing import set_start_method

from common.constants import BASE_NN_OUT_FEATURES_NUM, Constant
from epochs_statistics.utils import (
    init_epochs_best_dir,
    init_log_file,
    init_tables_file,
)
from ml.utils import (
    load_model_with_last_layer,
    model_weights_with_random_last_layer,
    random_model_weights,
)
from selection.crossover_type import CrossoverType
from selection.mutation_type import MutationType
from selection.parent_selection_type import ParentSelectionType
from timer.context_managers import manage_inference_stats

logging.basicConfig(
    level=logging.INFO,
    filename="app.log",
    filemode="a",
    format="%(asctime)s - p%(process)d: %(name)s - [%(levelname)s]: %(message)s",
)

import os

os.environ["NUMEXPR_NUM_THREADS"] = "1"

from r_learn import fitness_function, on_generation


def weights_vector(
    weights: list[float], model_path: str = Constant.IMPORTED_DICT_MODEL_PATH
):
    model = load_model_with_last_layer(
        model_path,
        weights,
    )
    assert len(weights) == BASE_NN_OUT_FEATURES_NUM
    return pygad.torchga.model_weights_as_vector(model)


def n_random_model_weights(
    n: int, low: float, hi: float, model_path: str = Constant.IMPORTED_DICT_MODEL_PATH
):
    rv = [
        random_model_weights(low=low, hi=hi, model_load_path=model_path)
        for _ in range(n)
    ]
    return rv


def n_random_last_layer_model_weights(
    n: int, low: float, hi: float, model_path: str = Constant.IMPORTED_DICT_MODEL_PATH
):
    rv = [
        model_weights_with_random_last_layer(low=low, hi=hi, model_load_path=model_path)
        for _ in range(n)
    ]
    return rv


def main():
    set_start_method("spawn")
    init_tables_file()
    init_log_file()
    init_epochs_best_dir()

    with manage_inference_stats():
        server_count = 8

        num_models_with_random_last_layer = 8
        num_random_models = 4

        num_generations = 6
        num_parents_mating = 6
        keep_parents = 2
        parent_selection_type = ParentSelectionType.STEADY_STATE_SELECTION
        crossover_type = CrossoverType.SINGLE_POINT
        mutation_type = MutationType.RANDOM
        mutation_percent_genes = 30
        random_mutation_max_val = 5.0
        random_mutation_min_val = -5.0
        random_init_weights_max_val = 5.0
        random_init_weights_min_val = -5.0

        initial_weights = []

        pre_loaded_last_layer1 = weights_vector(
            [
                -0.7853140655460631,
                0.7524892603731441,
                0.2844810949678288,
                -0.6819831165289404,
                -0.0830326280153653,
                0.1779108098019602,
                0.95478059636744,
                0.27937866719070503,
            ],
        )
        initial_weights.append(pre_loaded_last_layer1)

        pre_loaded_last_layer2 = weights_vector(
            [
                -0.7853139452883172,
                0.752490045931864,
                0.2844807733073216,
                -0.6819766889604519,
                -0.08303258833890134,
                0.17791068654815034,
                0.9555442824877577,
                0.2793786892860371,
            ]
        )
        initial_weights.append(pre_loaded_last_layer2)

        with_random_last_layer_weights = n_random_last_layer_model_weights(
            n=num_models_with_random_last_layer,
            low=random_init_weights_min_val,
            hi=random_init_weights_max_val,
        )

        initial_weights += with_random_last_layer_weights

        with_random_weights = n_random_model_weights(
            n=num_random_models,
            low=random_init_weights_min_val,
            hi=random_init_weights_max_val,
        )

        initial_weights += with_random_weights

        ga_instance = pygad.GA(
            num_generations=num_generations,
            num_parents_mating=num_parents_mating,
            initial_population=initial_weights,
            fitness_func=fitness_function,
            on_generation=on_generation,
            parallel_processing=["process", server_count],
            parent_selection_type=parent_selection_type,
            keep_parents=keep_parents,
            crossover_type=crossover_type,
            mutation_type=mutation_type,
            mutation_percent_genes=mutation_percent_genes,
            random_mutation_max_val=random_mutation_max_val,
            random_mutation_min_val=random_mutation_min_val,
        )

        ga_instance.run()
        ga_instance.save("./last_ga_instance")


if __name__ == "__main__":
    main()
