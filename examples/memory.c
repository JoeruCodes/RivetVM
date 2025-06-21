
volatile int arr[5];

int main() {
    arr[0] = 1;
    arr[1] = 2;
    arr[2] = arr[0] + arr[1];
    return arr[2]; 
} 