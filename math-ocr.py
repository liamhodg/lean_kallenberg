#!/usr/bin/env python3
import sys
import os
import warnings

# 1. Instantly kill Hugging Face hub progress bars and logging noise
os.environ["HF_HUB_DISABLE_PROGRESS_BARS"] = "1"
os.environ["TOKENIZERS_PARALLELISM"] = "false"
os.environ["HF_HUB_DISABLE_SYMLINKS_WARNING"] = "1"

warnings.filterwarnings("ignore")

try:
    import transformers
    transformers.utils.logging.set_verbosity_error()
    
    from mlx_vlm import load, generate
    from mlx_vlm.prompt_utils import apply_chat_template
    from mlx_vlm.utils import load_config
except ImportError:
    print("Error: Missing required packages. Run: pip install mlx-vlm transformers", file=sys.stderr)
    sys.exit(1)

def main():
    if len(sys.argv) < 2:
        print("Usage: math-ocr <path_to_image.png>", file=sys.stderr)
        sys.exit(1)

    image_path = sys.argv[1]

    if not os.path.exists(image_path):
        print(f"Error: File '{image_path}' not found.", file=sys.stderr)
        sys.exit(1)

    model_name = "mlx-community/DeepSeek-OCR-2-8bit"
    
    # 2. Capture the actual system file descriptors
    stdout_fd = sys.stdout.fileno()
    stderr_fd = sys.stderr.fileno()
    
    # Duplicate original stdout so we can restore it later
    saved_stdout_fd = os.dup(stdout_fd)
    
    try:
        # Redirect all System-Level stdout (1) to stderr (2).
        # This catches C++, Metal layer, and deep library prints.
        os.dup2(stderr_fd, stdout_fd)
        
        # Everything executed in this block outputs to stderr
        model, processor = load(model_name)
        config = load_config(model_name)

        prompt = "<|grounding|>Convert the document to markdown."
        formatted_prompt = apply_chat_template(processor, config, prompt, num_images=1)

        raw_output = generate(
            model,
            processor,
            formatted_prompt,
            [image_path],
            max_tokens=2048,
            temperature=0.0,
            verbose=False
        )
    finally:
        # 3. Restore the true system stdout descriptor right before printing the final payload
        sys.stdout.flush()
        os.dup2(saved_stdout_fd, stdout_fd)
        os.close(saved_stdout_fd)

    # Clean up the output text
    extracted_text = raw_output.text if hasattr(raw_output, 'text') else str(raw_output)
    extracted_text = extracted_text.replace("Ġ", " ").replace("Ċ", "\n")
    
    for tag in ["<|assistant|>", "<|endoftext|>", "<s>", "</s>"]:
        extracted_text = extracted_text.replace(tag, "")
        
    extracted_text = extracted_text.strip()

    # This is now the ONLY thing that will ever reach stdout
    print(extracted_text)

if __name__ == "__main__":
    main()